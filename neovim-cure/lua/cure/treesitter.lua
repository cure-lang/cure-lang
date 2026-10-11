local M = {}

-- The plugin lives in the Cure repository next to the grammar, so the parser
-- is compiled from `tree-sitter-cure/src/parser.c` without fetching anything.
local plugin_root = vim.fn.fnamemodify(debug.getinfo(1, "S").source:sub(2), ":p:h:h:h")

local building = false

--- Directory holding the grammar sources (`src/parser.c`).
---@param config table|nil
---@return string
function M.grammar_dir(config)
  if config and config.grammar_dir then
    return (vim.fn.fnamemodify(config.grammar_dir, ":p"):gsub("/$", ""))
  end
  return (vim.fn.fnamemodify(plugin_root .. "/../tree-sitter-cure", ":p"):gsub("/$", ""))
end

--- Where the compiled parser goes. `parser/` under the plugin is on the
--- runtimepath, which is where Neovim looks for `parser/cure.so`.
---@return string
function M.parser_path()
  return plugin_root .. "/parser/cure.so"
end

---@return string|nil
local function find_compiler()
  for _, cc in ipairs({ vim.env.CC or "", "cc", "gcc", "clang" }) do
    if cc ~= "" and vim.fn.executable(cc) == 1 then
      return cc
    end
  end
  return nil
end

---@param path string
---@return integer|nil
local function mtime(path)
  local stat = vim.uv.fs_stat(path)
  return stat and stat.mtime.sec or nil
end

--- True when the compiled parser is missing or older than `parser.c`.
---@param config table|nil
---@return boolean
function M.is_stale(config)
  local built = mtime(M.parser_path())
  local source = mtime(M.grammar_dir(config) .. "/src/parser.c")
  return built == nil or (source ~= nil and source > built)
end

--- True when Neovim can load a `cure` parser from the runtimepath.
---@return boolean
function M.has_parser()
  local ok, loaded = pcall(vim.treesitter.language.add, "cure")
  return ok and loaded ~= nil and loaded ~= false
end

--- Compile the parser into `parser/cure.so`.
---@param config table|nil
---@param on_done fun(ok: boolean, msg: string)|nil
function M.build(config, on_done)
  on_done = on_done or function(ok, msg)
    vim.notify(msg, ok and vim.log.levels.INFO or vim.log.levels.ERROR)
  end

  if building then
    return on_done(false, "cure: parser build already in progress")
  end

  local src = M.grammar_dir(config) .. "/src"
  if not vim.uv.fs_stat(src .. "/parser.c") then
    return on_done(false, "cure: grammar sources not found at " .. src)
  end

  local cc = find_compiler()
  if not cc then
    return on_done(false, "cure: no C compiler found (set $CC) to build the tree-sitter parser")
  end

  local out = M.parser_path()
  vim.fn.mkdir(vim.fn.fnamemodify(out, ":h"), "p")
  -- Build to a temporary name and rename, so a running Neovim never loads a
  -- half-written library and concurrent builds do not share a file.
  local tmp = ("%s.%d.tmp"):format(out, vim.uv.os_getpid())

  building = true
  vim.system(
    { cc, "-shared", "-fPIC", "-O2", "-I", src, src .. "/parser.c", "-o", tmp },
    { text = true },
    vim.schedule_wrap(function(result)
      building = false
      if result.code ~= 0 then
        os.remove(tmp)
        return on_done(false, "cure: building the tree-sitter parser failed:\n" .. (result.stderr or ""))
      end
      local ok, err = os.rename(tmp, out)
      if not ok then
        os.remove(tmp)
        return on_done(false, "cure: could not install " .. out .. ": " .. tostring(err))
      end
      on_done(true, "cure: built tree-sitter parser at " .. out)
    end)
  )
end

--- Start tree-sitter highlighting on every loaded Cure buffer.
local function start_all()
  for _, buf in ipairs(vim.api.nvim_list_bufs()) do
    if vim.api.nvim_buf_is_loaded(buf) and vim.bo[buf].filetype == "cure" then
      M.start(buf)
    end
  end
end

--- Highlight `bufnr` with tree-sitter. Returns false (leaving the regex
--- syntax in place) when no parser is available.
---@param bufnr integer
---@return boolean
function M.start(bufnr)
  if not M.has_parser() then
    return false
  end
  return (pcall(vim.treesitter.start, bufnr, "cure"))
end

--- Buffer entry point: use tree-sitter when the parser is there, otherwise
--- build it in the background (when allowed) and fall back to `syntax/cure.vim`
--- until it is ready.
---@param bufnr integer
---@param config table
function M.attach(bufnr, config)
  if config.enabled == false or vim.fn.has("nvim-0.11") == 0 then
    return
  end

  local loaded = M.has_parser()
  if loaded then
    M.start(bufnr)
  end

  -- A library Neovim already loaded cannot be swapped in this session, so a
  -- rebuild of a stale parser takes effect on the next start.
  if config.auto_install ~= false and M.is_stale(config) and find_compiler() then
    M.build(config, function(ok, msg)
      if not ok then
        vim.notify(msg, vim.log.levels.WARN)
      elseif not loaded then
        start_all()
      end
    end)
  end
end

-- Captures in the shared queries that Neovim has no default group for. Dotted
-- captures not listed here fall back to their parent (`@keyword.special` ->
-- `@keyword`).
local links = {
  ["@title.cure"] = "@module",
  ["@comment.doc.cure"] = "@comment.documentation",
  ["@string.regex.cure"] = "@string.regexp",
}

function M.set_highlights()
  for group, target in pairs(links) do
    vim.api.nvim_set_hl(0, group, { link = target, default = true })
  end
end

return M
