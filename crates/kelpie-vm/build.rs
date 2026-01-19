fn main() {
    let target_os = std::env::var("CARGO_CFG_TARGET_OS").unwrap_or_default();
    let vz_enabled = std::env::var("CARGO_FEATURE_VZ").is_ok();

    if vz_enabled && target_os == "macos" {
        cc::Build::new()
            .file("src/backends/vz_bridge.m")
            .flag("-fobjc-arc")
            .compile("kelpie_vz_bridge");
        println!("cargo:rustc-link-lib=framework=Virtualization");
        println!("cargo:rustc-link-lib=framework=Foundation");
    }
}
