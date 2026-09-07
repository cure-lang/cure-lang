use zed_extension_api::{self as zed, Result};

struct CureExtension;

impl zed::Extension for CureExtension {
    fn new() -> Self {
        CureExtension
    }

    fn language_server_command(
        &mut self,
        _language_server_id: &zed::LanguageServerId,
        worktree: &zed::Worktree,
    ) -> Result<zed::Command> {
        // 1. Check PATH for cure-lsp
        if let Some(path) = worktree.which("cure-lsp") {
            return Ok(zed::Command {
                command: path,
                args: vec![],
                env: vec![],
            });
        }

        // 2. Check worktree local binary ./cure-lsp
        let local_lsp = format!("{}/cure-lsp", worktree.root_path());
        return Ok(zed::Command {
            command: local_lsp,
            args: vec![],
            env: vec![],
        });
    }
}

zed::register_extension!(CureExtension);
