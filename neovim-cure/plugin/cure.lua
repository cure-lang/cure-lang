if vim.g.loaded_cure then
  return
end
vim.g.loaded_cure = true

require("cure").bootstrap()
