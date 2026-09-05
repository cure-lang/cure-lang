-- Vim ftplugin for Cure programming language
if vim.b.did_ftplugin then
  return
end
vim.b.did_ftplugin = true

local setlocal = vim.opt_local

setlocal.commentstring = "# %s"
setlocal.tabstop = 2
setlocal.shiftwidth = 2
setlocal.softtabstop = 2
setlocal.expandtab = true
setlocal.iskeyword:append("!,?,@")

-- Define buffer-local commands if cure module is loaded
local cure_ok, cure = pcall(require, "cure")
if cure_ok then
  cure.setup_buffer_commands(0)
end
