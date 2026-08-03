#[path = "../../tools/source_patch_build.rs"]
mod source_patch_build;

fn main() {
    source_patch_build::generate();
}
