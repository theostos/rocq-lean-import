prelude

structure DepRec where
  proposition : Prop
  proof : proposition
  next : DepRec

def DepRec.getProof (r : DepRec) : r.proposition := r.proof
