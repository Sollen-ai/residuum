//! Keeps docs/language-reference.md from going stale: every `res` block on
//! that page is a complete module that must parse and elaborate, and the
//! output the page quotes for its FOUR example must still be produced.
use std::path::Path;

fn blocks() -> Vec<String> {
    let page = std::fs::read_to_string(
        Path::new(env!("CARGO_MANIFEST_DIR")).join("docs/language-reference.md"),
    )
    .unwrap();
    let mut blocks = Vec::new();
    let mut rest = page.as_str();
    while let Some(start) = rest.find("```res\n") {
        let body = &rest[start + "```res\n".len()..];
        let end = body.find("```").expect("closed res block");
        blocks.push(body[..end].to_string());
        rest = &body[end + 3..];
    }
    blocks
}

#[test]
fn language_reference_examples_elaborate() {
    let blocks = blocks();
    assert!(blocks.len() >= 8, "{} res blocks", blocks.len());
    for block in &blocks {
        let name = block
            .lines()
            .find_map(|line| line.strip_prefix("module "))
            .expect("each res block declares a module");
        if let Err(error) = crate::parse_formal_to_typed(block) {
            panic!("docs/language-reference.md block `{name}`: {error}");
        }
    }
}

#[test]
fn language_reference_quoted_four_output_is_current() {
    let block = blocks()
        .into_iter()
        .find(|b| b.contains("module Queries"))
        .expect("Queries block");
    let module = crate::parse_formal_to_typed(&block).unwrap();
    let output =
        crate::experiments::render_results(&crate::experiments::run_experiments(&module).unwrap());
    assert!(output.contains("Horn: false\n"), "{output}");
    assert!(
        output.contains("FOUR least model: true (goal T; 2 atoms, 3 clauses; explicit scope)\n"),
        "{output}"
    );
}
