; ModuleID = 'while3.ll'
source_filename = "while3.c"
target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx11.0.0"

; Function Attrs: noinline nounwind optnone ssp uwtable
define i32 @test(i32 %arg) #0 {
bb:
  %i = alloca i32, align 4
  %i1 = alloca i32, align 4
  %i2 = alloca i32, align 4
  store i32 %arg, i32* %i, align 4
  store i32 0, i32* %i1, align 4
  store i32 1, i32* %i2, align 4
  br label %bb3

bb3:                                              ; preds = %bb7, %bb
  %i4 = load i32, i32* %i2, align 4
  %i5 = load i32, i32* %i, align 4
  %i6 = icmp slt i32 %i4, %i5
  br i1 %i6, label %bb15, label %bb16

bb7:                                              ; preds = %bb15
  %i8 = load i32, i32* %i1, align 4
  %i9 = load i32, i32* %i2, align 4
  %i10 = add nsw i32 %i8, %i9
  store i32 %i10, i32* %i1, align 4
  %i11 = load i32, i32* %i2, align 4
  %i12 = add nsw i32 %i11, 1
  store i32 %i12, i32* %i2, align 4
  br label %bb3

bb13:                                             ; preds = %bb16
  %i14 = load i32, i32* %i1, align 4
  ret i32 %i14

bb15:                                             ; preds = %bb3
  br label %bb7

bb16:                                             ; preds = %bb3
  br label %bb13
}

attributes #0 = { noinline nounwind optnone ssp uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+cx8,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }

!llvm.module.flags = !{!0, !1, !2}
!llvm.ident = !{!3}

!0 = !{i32 2, !"SDK Version", [2 x i32] [i32 11, i32 3]}
!1 = !{i32 1, !"wchar_size", i32 4}
!2 = !{i32 7, !"PIC Level", i32 2}
!3 = !{!"Homebrew clang version 11.1.0"}
