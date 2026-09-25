#!/usr/bin/env bash
# The development is layered by subject, and the layering is a claim about imports:
#
#   ForMathlib/ ──> Core/ ──> Braiding/ ──> Modules/ ──> TwoGen/ ──> Paper/
#       │                         └──> Examples/  ^
#       └──> Bergman/ ────────────────────────────┘
#
# Lake resolves modules package-wide, so nothing stops `Core/` importing `Modules/` except
# this check.  It also guards the property that makes the lower layers reusable: no module
# theory below `Modules/`.  `Bergman/` (the Bergman–Dicks realisation theorem) is ring theory
# with no κ-monoids, and sits beside `Core/` and `Braiding/` rather than above them.
set -uo pipefail
cd "$(dirname "$0")/.."
fail=0

# 1. Import discipline: which layers a file may import from.
allowed() {                      # $1 = layer of the importing file
  case "$1" in
    ForMathlib) echo "ForMathlib" ;;
    Core)       echo "ForMathlib Core" ;;
    Braiding)   echo "ForMathlib Core Braiding" ;;
    Examples)   echo "ForMathlib Core Braiding Examples" ;;
    Bergman)    echo "ForMathlib Bergman" ;;
    Modules)    echo "ForMathlib Core Braiding Bergman Modules" ;;
    TwoGen)     echo "ForMathlib Core Braiding Examples Bergman Modules TwoGen" ;;
    Paper)      echo "ForMathlib Core Braiding Examples Bergman Modules TwoGen Paper" ;;
    *)          echo "*" ;;
  esac
}

while IFS= read -r file; do
  rel=${file#KappaMonoid/}
  layer=${rel%%/*}; layer=${layer%.lean}
  ok=$(allowed "$layer")
  [ "$ok" = "*" ] && continue
  while IFS= read -r imp; do
    target=${imp#import KappaMonoid.}
    target=${target%%.*}
    [ "$target" = "$imp" ] && continue                   # not a repo import
    case " $ok " in
      *" $target "*) ;;
      *) echo "::error::$file (layer $layer) imports $target"; fail=1 ;;
    esac
  done < <(grep '^import KappaMonoid' "$file" || true)
done < <(find KappaMonoid -name '*.lean' | sort)

# 2. No module theory below `Modules/`.  `Core/` and `Braiding/` are monoid theory only —
#    that is what lets another development take them without Mathlib's module hierarchy.
if hits=$(grep -rlE '\bModuleClass\b|\[Ring |\[CommRing |\bIdeal \b|\bSubmodule\b' \
            KappaMonoid/Core KappaMonoid/Core.lean KappaMonoid/Braiding KappaMonoid/Braiding.lean \
            2>/dev/null); then
  [ -n "$hits" ] && { echo "::error::module theory under Core/ or Braiding/: $hits"; fail=1; }
fi

# 3. No file may import all of Mathlib except those that deliberately do.
while IFS= read -r file; do
  case "$file" in
    KappaMonoid/Modules/Small.lean) ;;
    # TEMPORARY: the files of the Bergman–Dicks proof still import all of Mathlib; their imports
    # are yet to be trimmed.  Nothing else in the development imports them except through the
    # aggregator, `KappaMonoid/Bergman.lean`.
    KappaMonoid/Bergman/*) ;;
    *) echo "::error::$file imports all of Mathlib; import what it uses instead"; fail=1 ;;
  esac
done < <(grep -rl '^import Mathlib$' KappaMonoid/ | sort)

[ $fail -eq 0 ] && echo "layering ok"
exit $fail
