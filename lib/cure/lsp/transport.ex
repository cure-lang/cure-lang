defmodule Cure.LSP.Transport do
  @moduledoc """
  LSP JSON-RPC 2.0 transport over stdio.

  Handles Content-Length header framing for reading and writing
  LSP messages on stdin/stdout.
  """

  @doc """
  Encode an LSP response/notification map to a framed binary.

  Produces `Content-Length: N\\r\\n\\r\\n{json}`.
  """
  @spec encode(map()) :: binary()
  def encode(message) do
    json = :json.encode(message) |> IO.iodata_to_binary()
    "Content-Length: #{byte_size(json)}\r\n\r\n#{json}"
  end

  @doc """
  Send an LSP message to stdout.
  """
  @spec send_message(map()) :: :ok
  def send_message(message) do
    IO.binwrite(encode(message))
  end

  @doc """
  Send a JSON-RPC response for a request with the given id.
  """
  @spec send_response(term(), term()) :: :ok
  def send_response(id, result) do
    send_message(%{"jsonrpc" => "2.0", "id" => id, "result" => result})
  end

  @doc """
  Send a JSON-RPC notification (no id).
  """
  @spec send_notification(String.t(), map()) :: :ok
  def send_notification(method, params) do
    send_message(%{"jsonrpc" => "2.0", "method" => method, "params" => params})
  end

  @doc """
  Send a JSON-RPC error response for a request with the given id.

  `code` is a JSON-RPC error code (`-32601` method not found, `-32602` invalid
  params, `-32603` internal error, `-32700` parse error) and `message` is the
  human-readable reason. Without this, an unsupported request with an `id` left
  the client waiting forever for a reply that never came.
  """
  @spec send_error(term(), integer(), String.t()) :: :ok
  def send_error(id, code, message) do
    send_message(%{"jsonrpc" => "2.0", "id" => id, "error" => %{"code" => code, "message" => message}})
  end

  @doc """
  Parse a buffer that may contain one or more framed LSP messages.

  Returns `{messages, remaining_buffer}` where `messages` is a list of
  decoded maps and `remaining_buffer` is leftover data.
  """
  @spec parse_buffer(binary()) :: {[map()], binary()}
  def parse_buffer(buffer) do
    parse_buffer(buffer, [])
  end

  defp parse_buffer(buffer, acc) do
    case parse_one(buffer) do
      {:ok, message, rest} -> parse_buffer(rest, [message | acc])
      :incomplete -> {Enum.reverse(acc), buffer}
    end
  end

  defp parse_one(buffer) do
    case :binary.split(buffer, "\r\n\r\n") do
      [header, rest] ->
        case parse_content_length(header) do
          {:ok, cl} when byte_size(rest) >= cl ->
            content = binary_part(rest, 0, cl)
            remaining = binary_part(rest, cl, byte_size(rest) - cl)

            case safe_json_decode(content) do
              {:ok, message} -> {:ok, message, remaining}
              :error -> :incomplete
            end

          _ ->
            :incomplete
        end

      _ ->
        :incomplete
    end
  end

  defp parse_content_length(header) do
    header
    |> String.split("\r\n")
    |> Enum.find_value(:error, fn line ->
      case String.split(line, ": ", parts: 2) do
        ["Content-Length", length_str] ->
          {:ok, String.to_integer(String.trim(length_str))}

        _ ->
          nil
      end
    end)
  end

  defp safe_json_decode(binary) do
    {:ok, :json.decode(binary)}
  rescue
    _ -> :error
  end
end
