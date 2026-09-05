local M = {}

local job_id = nil
local request_id = 0
local pending_requests = {}
local buffer_output = ""

--- Determine command to run Cure MCP server
---@param custom_cmd string[]|nil
---@return string[]
function M.get_mcp_cmd(custom_cmd)
  if custom_cmd and #custom_cmd > 0 then
    return custom_cmd
  end

  if vim.fn.executable("cure") == 1 then
    return { "cure", "mcp" }
  end

  local cwd = vim.fn.getcwd()
  local local_cure = cwd .. "/cure"
  if vim.fn.executable(local_cure) == 1 then
    return { local_cure, "mcp" }
  end

  if vim.fn.executable("mix") == 1 then
    return { "mix", "cure.mcp" }
  end

  return { "cure", "mcp" }
end

--- Start background MCP server process
---@param config table|nil
function M.start_server(config)
  if job_id then
    return true
  end

  config = config or {}
  local cmd = M.get_mcp_cmd(config.cmd)

  job_id = vim.fn.jobstart(cmd, {
    on_stdout = function(_, data, _)
      if not data then return end
      for _, line in ipairs(data) do
        if line ~= "" then
          buffer_output = buffer_output .. line
          local ok, req_resp = pcall(vim.json.decode, buffer_output)
          if ok and req_resp then
            buffer_output = ""
            if req_resp.id and pending_requests[req_resp.id] then
              local callback = pending_requests[req_resp.id]
              pending_requests[req_resp.id] = nil
              callback(req_resp)
            end
          end
        end
      end
    end,
    on_stderr = function(_, _, _) end,
    on_exit = function(_, _, _)
      job_id = nil
    end,
    pty = false,
  })

  if job_id and job_id > 0 then
    -- Send initialize request
    M.request("initialize", {}, function(_) end)
    return true
  else
    job_id = nil
    return false
  end
end

--- Stop background MCP server
function M.stop_server()
  if job_id then
    vim.fn.jobstop(job_id)
    job_id = nil
  end
end

--- Send a JSON-RPC request to the MCP server
---@param method string
---@param params table
---@param callback function
function M.request(method, params, callback)
  if not job_id then
    if not M.start_server() then
      callback({ error = { message = "Failed to start Cure MCP server process." } })
      return
    end
  end

  request_id = request_id + 1
  local id = request_id
  pending_requests[id] = callback

  local payload = {
    jsonrpc = "2.0",
    id = id,
    method = method,
    params = params or {},
  }

  local json_str = vim.json.encode(payload) .. "\n"
  vim.fn.chansend(job_id, json_str)
end

--- Call an MCP tool on Cure server
---@param tool_name string
---@param args table
---@param callback function
function M.call_tool(tool_name, args, callback)
  M.request("tools/call", {
    name = tool_name,
    arguments = args or {},
  }, function(resp)
    if resp.error then
      callback(false, resp.error.message or "MCP Error")
      return
    end

    local result = resp.result or {}
    if result.isError then
      local err_text = ""
      if result.content then
        for _, c in ipairs(result.content) do
          err_text = err_text .. (c.text or "")
        end
      end
      callback(false, err_text)
    else
      local out_text = ""
      if result.content then
        for _, c in ipairs(result.content) do
          out_text = out_text .. (c.text or "")
        end
      end
      callback(true, out_text)
    end
  end)
end

--- Open floating window with text content
---@param title string
---@param text string
---@param filetype string|nil
local function open_float_win(title, text, filetype)
  local lines = vim.split(text, "\n", { plain = true })

  local width = math.min(math.floor(vim.o.columns * 0.8), 100)
  local height = math.min(math.floor(vim.o.lines * 0.8), #lines + 2)
  if height < 3 then height = 5 end

  local buf = vim.api.nvim_create_buf(false, true)
  vim.api.nvim_buf_set_lines(buf, 0, -1, false, lines)

  if filetype then
    vim.bo[buf].filetype = filetype
  end

  vim.bo[buf].modifiable = false
  vim.bo[buf].bufhidden = "wipe"

  local row = math.floor((vim.o.lines - height) / 2)
  local col = math.floor((vim.o.columns - width) / 2)

  local win = vim.api.nvim_open_win(buf, true, {
    relative = "editor",
    width = width,
    height = height,
    row = row,
    col = col,
    style = "minimal",
    border = "rounded",
    title = " " .. title .. " ",
    title_pos = "center",
  })

  -- Keymaps to close floating window
  local opts = { noremap = true, silent = true }
  vim.api.nvim_buf_set_keymap(buf, "n", "q", "<cmd>close<cr>", opts)
  vim.api.nvim_buf_set_keymap(buf, "n", "<esc>", "<cmd>close<cr>", opts)
end

--- Display stdlib documentation in a float window
---@param module_name string|nil
function M.get_docs(module_name)
  if not module_name or module_name == "" then
    local current_word = vim.fn.expand("<cword>")
    if current_word:match("^Std%.") then
      module_name = current_word
    else
      module_name = vim.fn.input("Cure Stdlib Module (e.g. Std.List): ", "Std.List")
    end
  end

  if module_name == "" then return end

  M.call_tool("get_stdlib_docs", { module = module_name }, function(success, res)
    if success then
      open_float_win("Cure Stdlib Docs: " .. module_name, res, "markdown")
    else
      vim.notify("Cure MCP Error: " .. res, vim.log.levels.ERROR)
    end
  end)
end

--- Display syntax topic help in a float window
---@param topic string|nil
function M.get_help(topic)
  local topics = { "functions", "types", "fsm", "interfaces", "pattern_matching", "modules", "records" }

  local fetch_help = function(t)
    M.call_tool("get_syntax_help", { topic = t }, function(success, res)
      if success then
        open_float_win("Cure Syntax Help: " .. t, res, "markdown")
      else
        vim.notify("Cure MCP Error: " .. res, vim.log.levels.ERROR)
      end
    end)
  end

  if topic and topic ~= "" then
    fetch_help(topic)
  else
    vim.ui.select(topics, { prompt = "Select Cure Syntax Topic:" }, function(choice)
      if choice then
        fetch_help(choice)
      end
    end)
  end
end

--- Run type checker on current buffer via MCP
function M.type_check_buffer()
  local lines = vim.api.nvim_buf_get_lines(0, 0, -1, false)
  local source = table.concat(lines, "\n")

  vim.notify("Running Cure MCP type check...", vim.log.levels.INFO)
  M.call_tool("type_check_cure", { source = source }, function(success, res)
    if success then
      open_float_win("Cure MCP Type Check Result", res, "cure")
    else
      open_float_win("Cure MCP Type Check Errors", res, "cure")
    end
  end)
end

--- Run parser AST summary on current buffer via MCP
function M.parse_buffer()
  local lines = vim.api.nvim_buf_get_lines(0, 0, -1, false)
  local source = table.concat(lines, "\n")

  M.call_tool("parse_cure", { source = source }, function(success, res)
    if success then
      open_float_win("Cure MetaAST Summary", res, "elixir")
    else
      open_float_win("Cure Parse Error", res, "cure")
    end
  end)
end

--- Helper configuration export for CodeCompanion / Avante integration
function M.get_codecompanion_tool_config()
  local cmd = M.get_mcp_cmd()
  return {
    name = "cure_mcp",
    cmd = cmd[1],
    args = { unpack(cmd, 2) },
    description = "Cure programming language compiler, type-checker, and stdlib documentation MCP server.",
  }
end

return M
