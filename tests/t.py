from llvmlite import binding as llvm

asm_sum = r"""
define i32 @foo(i32 %arg) #0 {
bb:
  %tmp = alloca i32, align 4
  %tmp1 = alloca i32, align 4
  store i32 %arg, i32* %tmp, align 4
  %tmp2 = load i32, i32* %tmp, align 4
  %tmp3 = icmp sgt i32 %tmp2, 10
  br i1 %tmp3, label %bb4, label %bb5

bb4:                                              ; preds = %bb
  store i32 1, i32* %tmp1, align 4
  br label %bb6

bb5:                                              ; preds = %bb
  store i32 2, i32* %tmp1, align 4
  br label %bb6

bb6:                                              ; preds = %bb5, %bb4
  %tmp7 = load i32, i32* %tmp1, align 4
  ret i32 %tmp7
}

"""

ref = llvm.parse_assembly(asm_sum, None)
fn = ref.get_function("foo")

for b in fn.blocks:
  for i in b.instructions:
    if i.opcode == "br":
      print("operands: %s" % [op.name for op in i.operands])
