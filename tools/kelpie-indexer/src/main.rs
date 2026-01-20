//! Kelpie Indexer - Deterministic codebase indexing tool
//!
//! TigerStyle: Builds structural indexes from source code using deterministic parsing.

use anyhow::{Context, Result};
use clap::{Parser, Subcommand};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::collections::HashMap;
use std::fs;
use std::path::{Path, PathBuf};
use syn::visit::Visit;
use walkdir::WalkDir;

#[derive(Parser)]
#[command(name = "kelpie-indexer")]
#[command(about = "Build structural indexes for the Kelpie codebase")]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// Build all indexes
    Full,
    /// Build only symbol index
    Symbols,
    /// Build only dependency graph
    Dependencies,
    /// Build only specific files (incremental)
    Incremental { files: Vec<String> },
}

#[derive(Debug, Serialize, Deserialize)]
struct SymbolIndex {
    version: String,
    description: String,
    built_at: String,
    git_sha: Option<String>,
    files: HashMap<String, FileSymbols>,
}

#[derive(Debug, Serialize, Deserialize)]
struct FileSymbols {
    symbols: Vec<Symbol>,
    imports: Vec<String>,
    exports_to: Vec<String>, // Populated later by dependency analysis
}

#[derive(Debug, Serialize, Deserialize)]
struct Symbol {
    name: String,
    kind: String,
    line: usize,
    visibility: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    signature: Option<String>,
}

#[derive(Debug, Serialize, Deserialize)]
struct DependencyGraph {
    version: String,
    description: String,
    built_at: String,
    git_sha: Option<String>,
    nodes: Vec<GraphNode>,
    edges: Vec<GraphEdge>,
}

#[derive(Debug, Serialize, Deserialize)]
struct GraphNode {
    id: String,
    #[serde(rename = "type")]
    node_type: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    crate_name: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    file: Option<String>,
}

#[derive(Debug, Serialize, Deserialize)]
struct GraphEdge {
    from: String,
    to: String,
    #[serde(rename = "type")]
    edge_type: String,
}

struct SymbolVisitor {
    symbols: Vec<Symbol>,
    imports: Vec<String>,
}

impl SymbolVisitor {
    fn new() -> Self {
        Self {
            symbols: Vec::new(),
            imports: Vec::new(),
        }
    }

    fn visibility_to_string(vis: &syn::Visibility) -> String {
        match vis {
            syn::Visibility::Public(_) => "pub".to_string(),
            syn::Visibility::Restricted(r) => {
                format!("pub({})", quote::quote!(#r).to_string())
            }
            syn::Visibility::Inherited => "private".to_string(),
        }
    }
}

impl<'ast> Visit<'ast> for SymbolVisitor {
    fn visit_item_struct(&mut self, node: &'ast syn::ItemStruct) {
        let vis = Self::visibility_to_string(&node.vis);
        // Line numbers require source mapping - set to 0 for now
        let line = 0;

        self.symbols.push(Symbol {
            name: node.ident.to_string(),
            kind: "struct".to_string(),
            line,
            visibility: vis,
            signature: None,
        });

        syn::visit::visit_item_struct(self, node);
    }

    fn visit_item_enum(&mut self, node: &'ast syn::ItemEnum) {
        let vis = Self::visibility_to_string(&node.vis);
        // Line numbers require source mapping - set to 0 for now
        let line = 0;

        self.symbols.push(Symbol {
            name: node.ident.to_string(),
            kind: "enum".to_string(),
            line,
            visibility: vis,
            signature: None,
        });

        syn::visit::visit_item_enum(self, node);
    }

    fn visit_item_trait(&mut self, node: &'ast syn::ItemTrait) {
        let vis = Self::visibility_to_string(&node.vis);
        // Line numbers require source mapping - set to 0 for now
        let line = 0;

        self.symbols.push(Symbol {
            name: node.ident.to_string(),
            kind: "trait".to_string(),
            line,
            visibility: vis,
            signature: None,
        });

        syn::visit::visit_item_trait(self, node);
    }

    fn visit_item_fn(&mut self, node: &'ast syn::ItemFn) {
        let vis = Self::visibility_to_string(&node.vis);
        // Line numbers require source mapping - set to 0 for now
        let line = 0;

        // Build function signature
        let sig = &node.sig;
        let asyncness = if sig.asyncness.is_some() {
            "async "
        } else {
            ""
        };
        let unsafety = if sig.unsafety.is_some() {
            "unsafe "
        } else {
            ""
        };

        let signature = format!(
            "{}{}fn {}(..)",
            asyncness,
            unsafety,
            sig.ident
        );

        self.symbols.push(Symbol {
            name: sig.ident.to_string(),
            kind: "fn".to_string(),
            line,
            visibility: vis,
            signature: Some(signature),
        });

        syn::visit::visit_item_fn(self, node);
    }

    fn visit_item_impl(&mut self, node: &'ast syn::ItemImpl) {
        // Extract impl methods
        let impl_type = match &*node.self_ty {
            syn::Type::Path(p) => p.path.segments.last().map(|s| s.ident.to_string()),
            _ => None,
        };

        for item in &node.items {
            if let syn::ImplItem::Fn(method) = item {
                let vis = Self::visibility_to_string(&method.vis);
                // Line numbers require source mapping - set to 0 for now
                let line = 0;

                let asyncness = if method.sig.asyncness.is_some() {
                    "async "
                } else {
                    ""
                };

                let signature = if let Some(ref impl_name) = impl_type {
                    format!("{}fn {}::{}(..)", asyncness, impl_name, method.sig.ident)
                } else {
                    format!("{}fn {}(..)", asyncness, method.sig.ident)
                };

                self.symbols.push(Symbol {
                    name: method.sig.ident.to_string(),
                    kind: "method".to_string(),
                    line,
                    visibility: vis,
                    signature: Some(signature),
                });
            }
        }

        syn::visit::visit_item_impl(self, node);
    }

    fn visit_item_use(&mut self, node: &'ast syn::ItemUse) {
        // Extract use statements
        let use_str = quote::quote!(#node).to_string();
        // Clean up the string (remove "use" prefix and trailing semicolon)
        let cleaned = use_str
            .trim_start_matches("use")
            .trim()
            .trim_end_matches(';')
            .trim()
            .to_string();

        self.imports.push(cleaned);

        syn::visit::visit_item_use(self, node);
    }
}

fn parse_rust_file(path: &Path) -> Result<FileSymbols> {
    let content = fs::read_to_string(path)
        .with_context(|| format!("Failed to read file: {}", path.display()))?;

    let syntax = syn::parse_file(&content)
        .with_context(|| format!("Failed to parse file: {}", path.display()))?;

    let mut visitor = SymbolVisitor::new();
    visitor.visit_file(&syntax);

    Ok(FileSymbols {
        symbols: visitor.symbols,
        imports: visitor.imports,
        exports_to: Vec::new(), // Will be populated by dependency analysis later
    })
}

fn find_rust_files(root: &Path) -> Vec<PathBuf> {
    WalkDir::new(root)
        .into_iter()
        .filter_map(|e| e.ok())
        .filter(|e| e.path().extension().and_then(|s| s.to_str()) == Some("rs"))
        .filter(|e| {
            // Skip target directory and generated files
            let path_str = e.path().to_string_lossy();
            !path_str.contains("/target/") && !path_str.contains("/.cargo/")
        })
        .map(|e| e.path().to_path_buf())
        .collect()
}

fn build_symbol_index(workspace_root: &Path) -> Result<SymbolIndex> {
    let crates_dir = workspace_root.join("crates");
    if !crates_dir.exists() {
        anyhow::bail!("crates/ directory not found");
    }

    let rust_files = find_rust_files(&crates_dir);
    println!("Found {} Rust files to index", rust_files.len());

    let mut files = HashMap::new();

    for path in rust_files {
        let relative_path = path
            .strip_prefix(workspace_root)
            .unwrap_or(&path)
            .to_string_lossy()
            .to_string();

        match parse_rust_file(&path) {
            Ok(file_symbols) => {
                println!(
                    "  ✓ {} ({} symbols, {} imports)",
                    relative_path,
                    file_symbols.symbols.len(),
                    file_symbols.imports.len()
                );
                files.insert(relative_path, file_symbols);
            }
            Err(e) => {
                eprintln!("  ✗ {} - Error: {}", relative_path, e);
                // Continue with other files, don't fail entire index
            }
        }
    }

    // Get git SHA
    let git_sha = get_git_sha(workspace_root);

    Ok(SymbolIndex {
        version: "1.0.0".to_string(),
        description: "Symbol index: functions, structs, traits, impls".to_string(),
        built_at: chrono::Utc::now().to_rfc3339(),
        git_sha,
        files,
    })
}

fn get_git_sha(workspace_root: &Path) -> Option<String> {
    std::process::Command::new("git")
        .arg("rev-parse")
        .arg("HEAD")
        .current_dir(workspace_root)
        .output()
        .ok()
        .and_then(|output| {
            if output.status.success() {
                String::from_utf8(output.stdout).ok().map(|s| s.trim().to_string())
            } else {
                None
            }
        })
}

fn compute_file_hash(path: &Path) -> Result<String> {
    let content = fs::read(path)?;
    let hash = Sha256::digest(&content);
    Ok(format!("{:x}", hash))
}

fn update_freshness(workspace_root: &Path, files: &HashMap<String, FileSymbols>) -> Result<()> {
    let freshness_path = workspace_root.join(".kelpie-index/meta/freshness.json");

    let mut freshness: serde_json::Value = if freshness_path.exists() {
        let content = fs::read_to_string(&freshness_path)?;
        serde_json::from_str(&content)?
    } else {
        serde_json::json!({
            "version": "1.0.0",
            "description": "Tracks freshness of indexes for staleness detection",
            "git_sha": null,
            "updated_at": null,
            "file_hashes": {}
        })
    };

    // Update git SHA
    if let Some(git_sha) = get_git_sha(workspace_root) {
        freshness["git_sha"] = serde_json::Value::String(git_sha);
    }

    // Update timestamp
    freshness["updated_at"] = serde_json::Value::String(chrono::Utc::now().to_rfc3339());

    // Update file hashes
    let file_hashes = freshness["file_hashes"].as_object_mut().unwrap();
    for (file_path, _) in files {
        let full_path = workspace_root.join(file_path);
        if let Ok(hash) = compute_file_hash(&full_path) {
            file_hashes.insert(file_path.clone(), serde_json::Value::String(hash));
        }
    }

    // Write back
    let json = serde_json::to_string_pretty(&freshness)?;
    fs::write(freshness_path, json)?;

    Ok(())
}

fn build_dependency_graph(workspace_root: &Path) -> Result<DependencyGraph> {
    println!("Running cargo metadata...");

    let output = std::process::Command::new("cargo")
        .arg("metadata")
        .arg("--format-version=1")
        .arg("--no-deps")
        .current_dir(workspace_root)
        .output()
        .context("Failed to run cargo metadata")?;

    if !output.status.success() {
        anyhow::bail!("cargo metadata failed: {}", String::from_utf8_lossy(&output.stderr));
    }

    let metadata: serde_json::Value = serde_json::from_slice(&output.stdout)?;

    let mut nodes = Vec::new();
    let mut edges = Vec::new();

    // Extract packages (crates)
    if let Some(packages) = metadata["packages"].as_array() {
        for pkg in packages {
            let name = pkg["name"].as_str().unwrap_or("unknown");

            // Only include kelpie crates
            if !name.starts_with("kelpie") {
                continue;
            }

            // Add crate node
            nodes.push(GraphNode {
                id: name.to_string(),
                node_type: "crate".to_string(),
                crate_name: Some(name.to_string()),
                file: None,
            });

            // Add dependency edges
            if let Some(deps) = pkg["dependencies"].as_array() {
                for dep in deps {
                    let dep_name = dep["name"].as_str().unwrap_or("unknown");

                    // Only track dependencies between kelpie crates
                    if dep_name.starts_with("kelpie") {
                        edges.push(GraphEdge {
                            from: name.to_string(),
                            to: dep_name.to_string(),
                            edge_type: "depends".to_string(),
                        });
                    }
                }
            }
        }
    }

    println!("  Found {} kelpie crates", nodes.len());
    println!("  Found {} dependencies", edges.len());

    Ok(DependencyGraph {
        version: "1.0.0".to_string(),
        description: "Crate dependency graph from cargo metadata".to_string(),
        built_at: chrono::Utc::now().to_rfc3339(),
        git_sha: get_git_sha(workspace_root),
        nodes,
        edges,
    })
}

fn find_workspace_root() -> Result<PathBuf> {
    let mut current = std::env::current_dir()?;

    loop {
        let cargo_toml = current.join("Cargo.toml");
        if cargo_toml.exists() {
            // Check if this is a workspace root by looking for [workspace]
            let content = fs::read_to_string(&cargo_toml)?;
            if content.contains("[workspace]") {
                return Ok(current);
            }
        }

        // Move up one directory
        if let Some(parent) = current.parent() {
            current = parent.to_path_buf();
        } else {
            anyhow::bail!("Could not find workspace root (Cargo.toml with [workspace])");
        }
    }
}

fn main() -> Result<()> {
    let cli = Cli::parse();

    // Determine workspace root
    let workspace_root = find_workspace_root()?;
    println!("Workspace root: {}", workspace_root.display());

    match cli.command {
        Commands::Full => {
            // Build both indexes
            println!("\n=== Building Symbol Index ===");
            let symbol_index = build_symbol_index(&workspace_root)?;

            let output_path = workspace_root.join(".kelpie-index/structural/symbols.json");
            let json = serde_json::to_string_pretty(&symbol_index)?;
            fs::write(&output_path, json)?;

            println!("\n✓ Symbol index written to {}", output_path.display());
            println!("  Total files indexed: {}", symbol_index.files.len());
            let total_symbols: usize = symbol_index.files.values().map(|f| f.symbols.len()).sum();
            println!("  Total symbols: {}", total_symbols);

            println!("\n=== Building Dependency Graph ===");
            let dep_graph = build_dependency_graph(&workspace_root)?;

            let output_path = workspace_root.join(".kelpie-index/structural/dependencies.json");
            let json = serde_json::to_string_pretty(&dep_graph)?;
            fs::write(&output_path, json)?;

            println!("\n✓ Dependency graph written to {}", output_path.display());
            println!("  Total nodes: {}", dep_graph.nodes.len());
            println!("  Total edges: {}", dep_graph.edges.len());

            // Update freshness tracking
            println!("\n=== Updating Freshness Tracking ===");
            update_freshness(&workspace_root, &symbol_index.files)?;
            println!("✓ Freshness tracking updated");
        }
        Commands::Symbols => {
            println!("\n=== Building Symbol Index ===");
            let index = build_symbol_index(&workspace_root)?;

            // Write to .kelpie-index/structural/symbols.json
            let output_path = workspace_root.join(".kelpie-index/structural/symbols.json");
            let json = serde_json::to_string_pretty(&index)?;
            fs::write(&output_path, json)?;

            println!("\n✓ Symbol index written to {}", output_path.display());
            println!("  Total files indexed: {}", index.files.len());
            let total_symbols: usize = index.files.values().map(|f| f.symbols.len()).sum();
            println!("  Total symbols: {}", total_symbols);

            // Update freshness tracking
            println!("\n=== Updating Freshness Tracking ===");
            update_freshness(&workspace_root, &index.files)?;
            println!("✓ Freshness tracking updated");
        }
        Commands::Dependencies => {
            println!("\n=== Building Dependency Graph ===");
            let graph = build_dependency_graph(&workspace_root)?;

            // Write to .kelpie-index/structural/dependencies.json
            let output_path = workspace_root.join(".kelpie-index/structural/dependencies.json");
            let json = serde_json::to_string_pretty(&graph)?;
            fs::write(&output_path, json)?;

            println!("\n✓ Dependency graph written to {}", output_path.display());
            println!("  Total nodes: {}", graph.nodes.len());
            println!("  Total edges: {}", graph.edges.len());
        }
        Commands::Incremental { files } => {
            println!("Incremental indexing not yet implemented");
            println!("Files to index: {:?}", files);
        }
    }

    println!("\n✓ Indexing complete");

    Ok(())
}
