//! Renders the symbolic constraints and interactions of one AIR as a Lean module in the
//! `LeanZKCircuit_Plonky3` format the `PicoFV/RV64IM/Extraction/` files use.
//!
//! Adapted from an AIR-to-Lean constraint extractor by Nethermind (MIT/Apache-2.0); adapted to
//! Pico by Brevis.

use std::fmt::Write;

use p3_field::Field;
use pico_mle_core::{
    air::symbolic::{
        symbolic_expression::SymbolicExpression, symbolic_variable::Entry, SymbolicConstraints,
    },
    lookup::{LookupScope, LookupSummary, LookupType},
};

/// Which side of a lookup an interaction comes from. The symbolic builder records `looking` with
/// `count_weight = 1` and `looked` with `count_weight = 0`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Direction {
    Looking,
    Looked,
}

/// Everything rendered for one AIR.
pub struct ExtractedAir<F> {
    /// Lean namespace prefix, e.g. `AddChip` → `namespace AddChip.Extraction`.
    pub name: String,
    pub constraints: SymbolicConstraints<F>,
    /// `(direction, scope)` per entry of `constraints.interactions`, in the same order.
    pub interaction_meta: Vec<(Direction, LookupScope)>,
}

/// Pairs each interaction with the `(kind, scope)` summary the builder recorded for it. The
/// builder keeps looking and looked summaries in two lists, each in call order.
pub fn pair_interaction_meta<F: Field>(
    constraints: &SymbolicConstraints<F>,
    looking: &[LookupSummary],
    looked: &[LookupSummary],
) -> Vec<(Direction, LookupScope)> {
    let (mut looking, mut looked) = (looking.iter(), looked.iter());
    let meta = constraints
        .interactions
        .iter()
        .map(|interaction| {
            let (direction, summary) = match interaction.count_weight {
                1 => (Direction::Looking, looking.next()),
                0 => (Direction::Looked, looked.next()),
                w => panic!("unexpected count_weight {w}"),
            };
            let summary = summary.expect("fewer lookup summaries than interactions");
            assert_eq!(
                summary.kind, interaction.kind,
                "summary out of step with interactions"
            );
            (direction, summary.scope)
        })
        .collect();
    assert!(
        looking.next().is_none() && looked.next().is_none(),
        "more lookup summaries than interactions"
    );
    meta
}

const CIRCUIT_ARGS: &str = "{C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] \
                            [Circuit F ExtF C] (c : C F ExtF)";

/// Renders the whole Lean module. `source` names the pico commit the AIR was evaluated at.
pub fn render_module<F: Field>(air: &ExtractedAir<F>, source: &str) -> String {
    let name = &air.name;
    let constraints = &air.constraints.constraints;
    let interactions = &air.constraints.interactions;
    assert_eq!(
        interactions.len(),
        air.interaction_meta.len(),
        "interaction meta out of step"
    );
    let mut out = String::new();

    writeln!(
        out,
        "--Extracted from pico commit \"{source}\" by extractor/. Do not edit."
    )
    .unwrap();
    out.push_str(
        "import Mathlib.Data.List.Defs\n\n\
         import LeanZKCircuit_Plonky3.Plonky3.Circuit\n\n\
         import PicoFV.RV64IM.Extraction.Attributes\n\n\
         open Plonky3\n\n\
         set_option linter.all false\n\n",
    );
    writeln!(out, "namespace {name}.Extraction").unwrap();
    writeln!(out, "--Num constraints: {}", constraints.len()).unwrap();
    writeln!(out, "--Constraints---").unwrap();
    for (idx, constraint) in constraints.iter().enumerate() {
        writeln!(
            out,
            "@[extracted_constraint_definition] def constraint_{idx} {CIRCUIT_ARGS} (row: ℕ) :=\n  {} = 0",
            expr(constraint)
        )
        .unwrap();
    }

    writeln!(out, "@[extracted_constraint_definition]").unwrap();
    writeln!(out, "def constrain_interactions {CIRCUIT_ARGS} :=").unwrap();
    let entries = interactions
        .iter()
        .zip(&air.interaction_meta)
        .map(|(interaction, (direction, scope))| {
            let message = std::iter::once(bus_tag(interaction.kind).to_string())
                .chain(interaction.message.iter().map(expr))
                .collect::<Vec<_>>()
                .join(", ");
            format!(
                "  -- {direction:?} {:?} ({scope:?})\n  ({}, [{message}])",
                interaction.kind,
                expr(&interaction.count)
            )
        })
        .collect::<Vec<_>>();
    // An air without interactions keeps the same `flatMap` shape, which the proofs unfold.
    let body = if entries.is_empty() {
        String::new()
    } else {
        format!("\n{}", entries.join(",\n"))
    };
    writeln!(
        out,
        "  Circuit.bus c = (List.range (Circuit.last_row c + 1)).flatMap (λ row => [{body}])"
    )
    .unwrap();

    writeln!(out, "@[constraint_and_interaction_simplification]").unwrap();
    writeln!(
        out,
        "def constraint_list {CIRCUIT_ARGS} (row: ℕ)\n: List Prop :=\n  ["
    )
    .unwrap();
    let list = (0..constraints.len())
        .map(|idx| format!("    constraint_{idx} c row"))
        .collect::<Vec<_>>()
        .join(",\n");
    if !list.is_empty() {
        writeln!(out, "{list}").unwrap();
    }
    writeln!(out, "  ]").unwrap();
    writeln!(out, "@[constraint_and_interaction_simplification]").unwrap();
    writeln!(
        out,
        "def allHold {CIRCUIT_ARGS} (row: ℕ)\n: Prop :=\n  constrain_interactions c ∧\n  List.Forall (·) (constraint_list c row)"
    )
    .unwrap();
    writeln!(out, "end {name}.Extraction").unwrap();
    out
}

/// The bus tag is the `LookupType` discriminant, which is what the LogUp fingerprint absorbs
/// (as `kind + 1`).
fn bus_tag(kind: LookupType) -> u16 {
    kind as u16
}

/// Renders an expression fully parenthesised, so Lean never has to resolve precedence.
fn expr<F: Field>(x: &SymbolicExpression<F>) -> String {
    match x {
        SymbolicExpression::Variable(v) => match v.entry {
            Entry::Main { part_index, offset } => {
                // Pico chips have a single, unpartitioned main trace.
                assert_eq!(part_index, 0, "partitioned main trace");
                format!(
                    "(Circuit.main c (column := {}) (row := row) (rotation := {offset}))",
                    v.index
                )
            }
            Entry::Preprocessed { offset } => format!(
                "(Circuit.preprocessed c (column := {}) (row := row) (rotation := {offset}))",
                v.index
            ),
            Entry::Public => format!("(Circuit.public_values c (index := {}))", v.index),
        },
        SymbolicExpression::IsFirstRow => "(Circuit.isFirstRow c row)".to_string(),
        SymbolicExpression::IsLastRow => "(Circuit.isLastRow c row)".to_string(),
        SymbolicExpression::IsTransition => "(Circuit.isTransitionRow c row)".to_string(),
        SymbolicExpression::Constant(c) => format!("{c}"),
        SymbolicExpression::Add { x, y, .. } => format!("({} + {})", expr(x), expr(y)),
        SymbolicExpression::Sub { x, y, .. } => format!("({} - {})", expr(x), expr(y)),
        SymbolicExpression::Neg { x, .. } => format!("-({})", expr(x)),
        SymbolicExpression::Mul { x, y, .. } => format!("({} * {})", expr(x), expr(y)),
    }
}
