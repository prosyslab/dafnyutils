include "{{CLASS_NAME}}Spec.dfy"
include "{{CLASS_NAME}}Core.dfy"
include "{{CLASS_NAME}}Proof.dfy"

module {{CLASS_NAME}} {
  import opened {{CLASS_NAME}}Spec

  module {{CLASS_NAME}}BenchmarkItem {
    method RunCore()
      ensures Spec()
    {
      // TODO: call the implementation and proof boundary.
      assert false;
    }
  }
}
