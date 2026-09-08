def checkpointIdentity (P : Prop) (h : P) : P := h
def checkpointSecond : (P : Prop) → P → P := checkpointIdentity
def checkpointLast : (P : Prop) → P → P := checkpointSecond
