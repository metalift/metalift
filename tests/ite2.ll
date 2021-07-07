; ModuleID = 'switch1.ll'
source_filename = "switch1.c"
target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.16.0"

; Function Attrs: noinline nounwind optnone ssp uwtable
define i32 @test(i32 %arg) #0 {
bb:
  %tmp = alloca i32, align 4
  %tmp5 = alloca i32, align 4
  store i32 %arg, i32* %tmp5, align 4
  %tmp6 = load i32, i32* %tmp5, align 4
  br label %NodeBlock3

NodeBlock3:                                       ; preds = %bb
  %Pivot4 = icmp slt i32 %tmp6, 2
  br i1 %Pivot4, label %LeafBlock, label %NodeBlock

NodeBlock:                                        ; preds = %NodeBlock3
  %Pivot = icmp slt i32 %tmp6, 3
  br i1 %Pivot, label %bb8, label %LeafBlock1

LeafBlock1:                                       ; preds = %NodeBlock
  %SwitchLeaf2 = icmp eq i32 %tmp6, 3
  br i1 %SwitchLeaf2, label %bb9, label %NewDefault

LeafBlock:                                        ; preds = %NodeBlock3
  %SwitchLeaf = icmp eq i32 %tmp6, 1
  br i1 %SwitchLeaf, label %bb7, label %NewDefault

bb7:                                              ; preds = %LeafBlock
  store i32 10, i32* %tmp, align 4
  br label %bb11

bb8:                                              ; preds = %NodeBlock
  store i32 20, i32* %tmp, align 4
  br label %bb11

bb9:                                              ; preds = %LeafBlock1
  store i32 30, i32* %tmp, align 4
  br label %bb11

NewDefault:                                       ; preds = %LeafBlock1, %LeafBlock
  br label %bb10

bb10:                                             ; preds = %NewDefault
  store i32 40, i32* %tmp, align 4
  br label %bb11

bb11:                                             ; preds = %bb10, %bb9, %bb8, %bb7
  %tmp12 = load i32, i32* %tmp, align 4
  ret i32 %tmp12
}

attributes #0 = { noinline nounwind optnone ssp uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+cx8,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }

!llvm.module.flags = !{!0, !1}
!llvm.ident = !{!2}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 7, !"PIC Level", i32 2}
!2 = !{!"clang version 10.0.0 "}
