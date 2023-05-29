; ModuleID = 'while5.ll'
source_filename = "while5.c"
target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx11.0.0"

; Function Attrs: noinline nounwind optnone ssp uwtable
define i32 @test() #0 {
bb:
  %i = alloca i32, align 4
  %i1 = alloca i32, align 4
  %i2 = alloca i32, align 4
  store i32 0, i32* %i, align 4
  store i32 1, i32* %i1, align 4
  br label %bb3

bb3:                                              ; preds = %bb6, %bb
  %i4 = load i32, i32* %i1, align 4
  %i5 = icmp slt i32 %i4, 3
  br i1 %i5, label %bb24, label %bb25

bb6:                                              ; preds = %bb24
  %i7 = load i32, i32* %i, align 4
  %i8 = load i32, i32* %i1, align 4
  %i9 = add nsw i32 %i7, %i8
  store i32 %i9, i32* %i, align 4
  %i10 = load i32, i32* %i1, align 4
  %i11 = add nsw i32 %i10, 1
  store i32 %i11, i32* %i1, align 4
  br label %bb3

bb12:                                             ; preds = %bb25
  store i32 1, i32* %i2, align 4
  br label %bb13

bb13:                                             ; preds = %bb16, %bb12
  %i14 = load i32, i32* %i2, align 4
  %i15 = icmp slt i32 %i14, 4
  br i1 %i15, label %bb26, label %bb27

bb16:                                             ; preds = %bb26
  %i17 = load i32, i32* %i, align 4
  %i18 = load i32, i32* %i2, align 4
  %i19 = add nsw i32 %i17, %i18
  store i32 %i19, i32* %i, align 4
  %i20 = load i32, i32* %i2, align 4
  %i21 = add nsw i32 %i20, 1
  store i32 %i21, i32* %i2, align 4
  br label %bb13

bb22:                                             ; preds = %bb27
  %i23 = load i32, i32* %i, align 4
  ret i32 %i23

bb24:                                             ; preds = %bb3
  br label %bb6

bb25:                                             ; preds = %bb3
  br label %bb12

bb26:                                             ; preds = %bb13
  br label %bb16

bb27:                                             ; preds = %bb13
  br label %bb22
}

attributes #0 = { noinline nounwind optnone ssp uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+cx8,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }

!llvm.module.flags = !{!0, !1, !2}
!llvm.ident = !{!3}

!0 = !{i32 2, !"SDK Version", [2 x i32] [i32 11, i32 3]}
!1 = !{i32 1, !"wchar_size", i32 4}
!2 = !{i32 7, !"PIC Level", i32 2}
!3 = !{!"Homebrew clang version 11.1.0"}
