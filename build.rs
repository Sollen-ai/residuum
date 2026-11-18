//! Test families (docs/compile-cost-optimizations.md, palanca 2).
//!
//! Each `family_*` cfg is set when its feature is enabled, or when no family
//! feature is enabled at all, so a plain `cargo test` still compiles every test.

const FAMILIES: [(&str, &str); 4] = [
    ("residual", "TEST_RESIDUAL"),
    ("experiments", "TEST_EXPERIMENTS"),
    ("legal_geometry", "TEST_LEGAL_GEOMETRY"),
    ("legal_learning", "TEST_LEGAL_LEARNING"),
];

fn main() {
    println!("cargo::rerun-if-changed=build.rs");
    let selecting = std::env::var_os("CARGO_FEATURE_TEST_FAMILIES").is_some();
    for (family, feature) in FAMILIES {
        println!("cargo::rustc-check-cfg=cfg(family_{family})");
        if !selecting || std::env::var_os(format!("CARGO_FEATURE_{feature}")).is_some() {
            println!("cargo::rustc-cfg=family_{family}");
        }
    }
}
