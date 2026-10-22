#!/usr/bin/env bash
# Type-check the whole mechanised-soundness development.
#
# Requires Agda 2.8.0 and the Agda standard library registered in
# ~/.config/agda/libraries (see proof/README.md).
set -euo pipefail

cd "$(dirname "$0")"

# ---------------------------------------------------------------------------
# Pre-flight: fail once, with an actionable message, instead of FAILing every
# module with the same environment error.
# ---------------------------------------------------------------------------
preflight_fail() {
  echo "pre-flight check failed: $1" >&2
  shift
  for line in "$@"; do echo "  $line" >&2; done
  exit 2
}

if ! command -v agda >/dev/null 2>&1; then
  preflight_fail "'agda' was not found in PATH." \
    "Install Agda 2.8.0 (e.g. 'sudo apt install agda' or 'cabal install Agda-2.8.0')."
fi
# Cap every Agda process, including pre-flight probes. This limits the GHC
# heap, not total RSS; override explicitly for a different machine budget.
AGDA=(agda +RTS "-M${AGDA_HEAP_LIMIT:-24G}" -RTS)

agda_version=$("${AGDA[@]}" --version | head -n1)
case "$agda_version" in
  *' 2.8.'*) ;;
  *) echo "warning: expected Agda 2.8.x, found: $agda_version" >&2 ;;
esac

# Probe: a throwaway library depending on 'standard-library' that imports a
# stdlib module. This resolves libraries exactly as the real modules will
# (AGDA_DIR, XDG config dir, ~/.agda, --library-file, ...).
probe_dir=$(mktemp -d)
trap 'rm -rf "$probe_dir"' EXIT
printf 'name: cure-preflight\ninclude: .\ndepend: standard-library\n' \
  > "$probe_dir/cure-preflight.agda-lib"
printf 'module Probe where\nopen import Data.Nat using (ℕ)\n' \
  > "$probe_dir/Probe.agda"

if ! probe_out=$(cd "$probe_dir" && "${AGDA[@]}" Probe.agda 2>&1); then
  app_dir=$("${AGDA[@]}" --print-agda-app-dir 2>/dev/null || echo "~/.config/agda")
  stdlib_hint=$(find /usr/share /usr/local/share "$HOME" -maxdepth 4 \
    -name standard-library.agda-lib 2>/dev/null | head -n1 || true)
  preflight_fail "the Agda standard library is not usable." \
    "Agda said:" \
    "$(echo "$probe_out" | head -n 8 | sed 's/^/    /')" \
    "" \
    "Register it by adding the path of its standard-library.agda-lib to" \
    "  $app_dir/libraries" \
    "for example:" \
    "  mkdir -p '$app_dir'" \
    "  echo '${stdlib_hint:-/path/to/standard-library.agda-lib}' >> '$app_dir/libraries'" \
    "See proof/README.md for details."
fi

MODULES=(
  Core/Grade Core/Universe Core/Syntax Core/Value Core/Reduction
  Core/Signature Core/Coverage Core/TypeHeads Core/Typing Core/ClosedFragment Core/Parallel
  Core/Relation Core/StrictParallel
  Core/LiteralExpansion
  Core/LocalFrame
  Proof/Values Proof/Inversion Proof/CanonicalForms Proof/Substitution
  Proof/Context Proof/FieldOrder
  Proof/Progress Proof/Preservation Proof/FinalPreservation Proof/Soundness
  Proof/StrictConfluence Proof/Confluence Proof/SoundnessConfluence Proof/Erase
  Proof/InterfaceAudit Proof/EffectInert
  Core/Verification Proof/VerificationExamples
  Proof/LiteralCases
  Proof/SpineLifting
  Proof/CoverageExamples
  Proof/ClosedFragmentExamples
  Proof/ConversionModel
  Proof/ConversionExamples
  Proof/ConfluenceExamples
  Proof/ExpansionSimulation Proof/ReductionConversion
  Proof/ReductionConversionExamples Proof/SoundnessModel
  Proof/LocalFrame Proof/DependentSpine Proof/DependentSpineExamples
  Proof/FieldOrderExamples
  Proof/DependentInstantiation
  Proof/DependentInstantiationExamples
  Proof/DependentResult
  Proof/DependentResultExamples
  Proof/DependentRegistry
  Proof/DependentRegistryExamples
  Proof/DependentPreservation
  Proof/DependentPreservationExamples
  Proof/DependentBranch
  Proof/DependentBranchExamples
  Proof/DependentOpening
  Proof/DependentOpeningExamples
  Proof/MotiveAgreement
  Proof/MotiveAgreementExamples
  Proof/MotiveBoundaryAudit
  Core/DependentTyping
  Proof/DependentTypingExamples
  Proof/DependentTypingInversion
  Proof/DependentMotiveControls
  Proof/DependentTypingControls
  Proof/DependentNaturality
  Proof/DependentCoherence
  Proof/DependentCoherenceExamples
  Proof/DependentTransport
  Proof/DependentTransportExamples
  Proof/DependentIota
  Proof/DependentIotaExamples
  Proof/DependentIotaBranchExamples
  Proof/DependentRootPreservation
  Proof/DependentRootExamples
  Proof/DependentScoping
  Proof/DependentScopedAlgebra
  Proof/DependentContextSuffix
  Proof/DependentContextSuffixExamples
  Proof/DependentDataConversion
  Proof/DependentConstructorInversion
  Proof/DependentConstructorInversionExamples
  Proof/DependentSpineConversion
  Proof/DependentSpineConversionExamples
  Proof/DependentGeneralTransport
  Proof/DependentGeneralTransportExamples
  Proof/DependentGeneralIota
  Proof/DependentGeneralIotaExamples
  Proof/DependentCongruence
  Proof/DependentCongruenceExamples
  Proof/DependentLiteralPreservation
  Proof/DependentLiteralExamples
  Proof/DependentLiteralBoundaryAudit
  Proof/DependentPreservationControls
  Proof/DependentSubjectReduction
  Proof/DependentSubjectReductionExamples
  Proof/DependentSubjectReductionLiterals
  Proof/DependentCanonical
  Proof/DependentProgress
  Proof/DependentProgressExamples
  Proof/DependentObservation
  Proof/DependentObservationExamples
  Proof/DependentSoundness
  Proof/DependentSoundnessModel
  Proof/DependentSoundnessExamples
  Proof/DependentSoundnessControls
  Core/CanonicalSnapshot
  Core/AdmissionBoundary
  Proof/AdmissionBoundaryExamples
  Proof/CanonicalSnapshotExamples
  Core/ExecutableSnapshot
  Fixtures/ExecutableSnapshot
  Core/AdmissionReplay
  Core/ExecutableReplay
  Proof/ExecutableSnapshotExamples
  Proof/AdmissionReplayControls
  Core/NativeCertificate
  Proof/NativeCertificateExamples
  Proof/NativeCertificateControls
  Proof/NativeCertificateSafety
  Core/SyntaxEquality
  Core/NativeRecipe
  Proof/NativeRecipeExamples
  Proof/NativeRecipeControls
  Core/Wire
  Proof/WireExamples
  Core/WireConversion
  Proof/WireConversionExamples
)

fail=0
for m in "${MODULES[@]}"; do
  printf '%-28s ' "$m"
  if out=$("${AGDA[@]}" "$m.agda" 2>&1); then
    if echo "$out" | grep -qiE 'warning'; then
      echo 'WARNINGS'; echo "$out" | grep -iE 'warning' | head -3; fail=1
    else
      echo 'OK'
    fi
  else
    echo 'FAIL'; echo "$out" | head -20; fail=1
  fi
done

exit "$fail"
