include "Spec.dfy"
include "Core.dfy"
include "Proof.dfy"

module {{CLASS_NAME}} {
  import opened {{CLASS_NAME}}Spec

  method RunCore()
    ensures Spec()
  {
    // TODO: call the implementation and proof boundary.
    assert false;
  }
}
