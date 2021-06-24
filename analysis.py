from vc import Block


def setupBlocks (blks):
  bbs = dict((b.name, Block(b.name, list(b.instructions))) for b in blks)

  for b in bbs.values():
    br = b.instructions[-1]
    if br.opcode == "br":
      operands = list(br.operands)
      targets = operands[0:] if len(operands) == 1 else operands[1:]
      b.succs = [bbs[t.name] for t in targets]
      #print("set %s pred to %s" % (b.name, ", ".join(t.name for t in targets)))
      for t in targets:
        bbs[t.name].preds.append(b)

  return bbs
