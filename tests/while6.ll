; ModuleID = 'while6.ll'
source_filename = "while6.c"
target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.16.0"

; Function Attrs: noinline nounwind optnone ssp uwtable
define i32 @test() #0 {
bb:
  %tmp = alloca i32, align 4
  %tmp1 = alloca i32, align 4
  %tmp2 = alloca i32, align 4
  store i32 0, i32* %tmp, align 4
  store i32 0, i32* %tmp1, align 4
  br label %bb3

bb3:                                              ; preds = %bb15, %bb
  %tmp4 = load i32, i32* %tmp1, align 4
  %tmp5 = icmp slt i32 %tmp4, 3
  br i1 %tmp5, label %bb6, label %bb18

bb6:                                              ; preds = %bb3
  store i32 0, i32* %tmp2, align 4
  br label %bb7

bb7:                                              ; preds = %bb10, %bb6
  %tmp8 = load i32, i32* %tmp2, align 4
  %tmp9 = icmp slt i32 %tmp8, 5
  br i1 %tmp9, label %bb10, label %bb15

bb10:                                             ; preds = %bb7
  %tmp11 = load i32, i32* %tmp, align 4
  %tmp12 = add nsw i32 %tmp11, 2
  store i32 %tmp12, i32* %tmp, align 4
  %tmp13 = load i32, i32* %tmp2, align 4
  %tmp14 = add nsw i32 %tmp13, 1
  store i32 %tmp14, i32* %tmp2, align 4
  br label %bb7

bb15:                                             ; preds = %bb7
  %tmp16 = load i32, i32* %tmp1, align 4
  %tmp17 = add nsw i32 %tmp16, 1
  store i32 %tmp17, i32* %tmp1, align 4
  br label %bb3

bb18:                                             ; preds = %bb3
  %tmp19 = load i32, i32* %tmp, align 4
  ret i32 %tmp19
}

attributes #0 = { noinline nounwind optnone ssp uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+cx8,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }

!llvm.module.flags = !{!0, !1}
!llvm.ident = !{!2}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 7, !"PIC Level", i32 2}
!2 = !{!"clang version 10.0.0 "}
