import Lake
open Lake DSL
require std from git "https://github.com/leanprover/std4" @ "nightly-testing"

package «SetTheory» {
  --leanOptions := []  -- add package configuration options here
}

@[default_target]
lean_lib «SetTheory» {
  -- add library configuration options here
}
