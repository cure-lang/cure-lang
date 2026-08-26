# test/cure/compiler/actor_quote_golden_test.exs
#
# SP5.1 Stage 5 — byte-identical-Core gate for the quasiquotation port.
#
# `derive_actor` and its helpers in lib/std/actor.cure are being rewritten from
# hand-built `Std.Syntax` builders to `quote`/`$( )`. The port is a pure
# refactor: the SAME generated GenServer module must come out. These goldens
# freeze the compiled BEAM of three representative generated modules, captured
# from the pre-port build (HEAD). Each module exercises a different slice of the
# expander:
#
#   * GDerived        — `derive` path: default_actor_init + actor_handler arms
#   * GStructuredCall — structured `on_call`: reply channel + handle_call
#   * GLifecycle      — optional terminate / code_change callback bodies
#   * GFsmDerived     — derive_fsm: callback_mode + init callback bodies
#   * GSup            — derive_supervisor: init %[:ok, %[strategy, children]]
#   * GApp            — derive_application: stop / start_phase :ok bodies
#
# If a hash here changes, the port altered the generated program — that is the
# failure this gate exists to catch. The ONLY legitimate reason to re-freeze is
# an intentional, separately-reviewed change to codegen or an OTP major bump
# that reshapes BEAM encoding; in that case recapture all three together and say
# so in the commit.
#
# Re-frozen for Task 2.6 (Equatable/Comparable as the sole route to `==`/`<`,
# with structural `Equatable` auto-derived for ADTs lacking a hand-written
# instance). GDerived, GStructuredCall, GFsmDerived and GLifecycle each declare
# their own message/event ADT (ActorMessage / ActorRequest / FsmEvent), so each
# now OWNS and emits exactly one auto-derived structural-equality method
# (`__impl_Equatable_<Module>#<Type>_==/2`) — an intentional codegen addition,
# verified as a single owned instance (not ambient bloat). The modules with no
# ADT of their own (Raw01/Raw15/Raw16, GSup, GApp) stay byte-identical: making
# Std.Equatable/Std.Comparable `@prelude` no longer duplicates their ~two dozen
# ambient instances into every consumer — owner-qualified instances now emit once
# in their owning module and are reached by remote call (see `check_ast_with_locals`).
#
# Re-frozen for typed actor Phase 2: structured actors intentionally add their
# nominal Handle plus validated start/send/stop adapters; call-capable actors
# also add request. This is a public generated-API change, not a quote-port
# refactor. The supervisor lifecycle-handle additions likewise update GSup's
# generated module; application output remains byte-identical.
#
# Artifact manifest v3 adds compiler/source/producer-snapshot provenance to every
# BEAM. That identity intentionally changes with the compiler fingerprint, so
# this gate hashes the disassembled generated program with only the provenance
# attribute removed rather than hashing the complete artifact bytes.
#
# Cast-only actors now emit a total fallback `handle_call/3`, completing the
# advertised `gen_server` behaviour and preserving state for raw BEAM callers.
# GLifecycle is the cast-only fixture, so this intentional generated-program
# addition changes only its semantic hash.
#
# Canonical computed-index branch instantiation now substitutes the constructor
# indices into each branch motive before erasure. GStructuredCall is the only
# fixture here whose generated request/reply path exercises that dependent
# motive; its typed actor API and OTP behavior are covered separately. The
# other three semantic hashes remain unchanged.
defmodule Cure.Compiler.ActorQuoteGoldenTest do
  use ExUnit.Case, async: false

  @samples [
    {"GStructuredCall",
     """
     mod M
       use Std.Actor

       actor Cure.Generated.GStructuredCall
         state Int
         on_cast
           Inc -> state + 1
         on_call Read() returns Int
           reply state

     fn make_request() -> ActorRequest = Read()
     """, "0dd122257591d90cb9668681586205a028b990bf6d7ccdae1171add1d8c33a52"},
    {"GSup",
     """
     mod M
       use Std.Supervisor

       sup Cure.Generated.GSup
         children []
     """, "bd1d926289582c1856e550749ae639f16ecc7ceb406154b7f93767c1e4d0dbb7"},
    {"GApp",
     """
     mod M
       use Std.App

       app Cure.Generated.GApp
         root Cure.Generated.GSup
     """, "6af20d5844d402df02186c4f899f74f012134a7409ae3c6eced73f5746684a16"},
    {"GLifecycle",
     """
     mod M
       use Std.Actor

       actor Cure.Generated.GLifecycle
         state Int
         on_cast
           Inc -> state + 1
         terminate :shutdown
         code_change %[:ok, state + 1]
     """, "09e776c7b3122e0f0ba6cb1922a2d3515a0f40f892ad8537db3893c21e642b19"}
  ]

  defp beam_sha256(name, src) do
    dir = Path.join(System.tmp_dir!(), "cure_actor_golden_#{name}_#{System.unique_integer([:positive])}")
    File.rm_rf!(dir)
    File.mkdir_p!(dir)

    try do
      assert {:ok, _module, _warnings} =
               Cure.Compiler.compile_string(src, output_dir: dir, emit_events: false)

      beam = Path.join(dir, "Cure.Generated.#{name}.beam")

      {:beam_file, module, exports, attributes, _compile_info, functions} =
        beam |> File.read!() |> :beam_disasm.file()

      semantic_program = {
        module,
        exports,
        Enum.reject(attributes, fn {name, _value} -> name == :cure_artifact end),
        functions
      }

      semantic_program
      |> :erlang.term_to_binary([:deterministic])
      |> then(&:crypto.hash(:sha256, &1))
      |> Base.encode16(case: :lower)
    after
      File.rm_rf!(dir)
    end
  end

  for {name, src, expected} <- @samples do
    test "generated #{name} module is byte-identical to the pre-port snapshot" do
      assert beam_sha256(unquote(name), unquote(src)) == unquote(expected)
    end
  end
end
