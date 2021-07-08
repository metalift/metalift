; ModuleID = 'while5.ll'
source_filename = "while5.c"
target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.16.0"

; Function Attrs: noinline nounwind optnone ssp uwtable
define i32 @test() #0 {
bb:
  %tmp = alloca i32, align 4
  %tmp1 = alloca i32, align 4
  %tmp2 = alloca i32, align 4
  store i32 0, i32* %tmp, align 4
  store i32 1, i32* %tmp1, align 4
  br label %bb3

bb3:                                              ; preds = %bb6, %bb
  %tmp4 = load i32, i32* %tmp1, align 4
  %tmp5 = icmp slt i32 %tmp4, 3
  br i1 %tmp5, label %bb6, label %bb12

bb6:                                              ; preds = %bb3
  %tmp7 = load i32, i32* %tmp, align 4
  %tmp8 = load i32, i32* %tmp1, align 4
  %tmp9 = add nsw i32 %tmp7, %tmp8
  store i32 %tmp9, i32* %tmp, align 4
  %tmp10 = load i32, i32* %tmp1, align 4
  %tmp11 = add nsw i32 %tmp10, 1
  store i32 %tmp11, i32* %tmp1, align 4
  br label %bb3

bb12:                                             ; preds = %bb3
  store i32 1, i32* %tmp2, align 4
  br label %bb13

bb13:                                             ; preds = %bb16, %bb12
  %tmp14 = load i32, i32* %tmp2, align 4
  %tmp15 = icmp slt i32 %tmp14, 4
  br i1 %tmp15, label %bb16, label %bb22

bb16:                                             ; preds = %bb13
  %tmp17 = load i32, i32* %tmp, align 4
  %tmp18 = load i32, i32* %tmp2, align 4
  %tmp19 = add nsw i32 %tmp17, %tmp18
  store i32 %tmp19, i32* %tmp, align 4
  %tmp20 = load i32, i32* %tmp2, align 4
  %tmp21 = add nsw i32 %tmp20, 1
  store i32 %tmp21, i32* %tmp2, align 4
  br label %bb13

bb22:                                             ; preds = %bb13
  %tmp23 = load i32, i32* %tmp, align 4
  ret i32 %tmp23
}

attributes #0 = { noinline nounwind optnone ssp uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+cx8,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }

!llvm.module.flags = !{!0, !1}
!llvm.ident = !{!2}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 7, !"PIC Level", i32 2}
!2 = !{!"clang version 10.0.0 "}
