; ModuleID = 'while4.ll'
source_filename = "while4.c"
target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx11.0.0"

; Function Attrs: noinline nounwind optnone ssp uwtable
define i32 @test() #0 {
bb:
  %i = alloca i32, align 4
  %i1 = alloca i32, align 4
  store i32 0, i32* %i, align 4
  store i32 1, i32* %i1, align 4
  br label %bb2

bb2:                                              ; preds = %bb5, %bb
  %i3 = load i32, i32* %i1, align 4
  %i4 = icmp slt i32 %i3, 3
  br i1 %i4, label %bb13, label %bb14

bb5:                                              ; preds = %bb13
  %i6 = load i32, i32* %i, align 4
  %i7 = load i32, i32* %i1, align 4
  %i8 = add nsw i32 %i6, %i7
  store i32 %i8, i32* %i, align 4
  %i9 = load i32, i32* %i1, align 4
  %i10 = add nsw i32 %i9, 1
  store i32 %i10, i32* %i1, align 4
  br label %bb2

bb11:                                             ; preds = %bb14
  %i12 = load i32, i32* %i, align 4
  ret i32 %i12

bb13:                                             ; preds = %bb2
  br label %bb5

bb14:                                             ; preds = %bb2
  br label %bb11
}

attributes #0 = { noinline nounwind optnone ssp uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+cx8,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }

!llvm.module.flags = !{!0, !1, !2}
!llvm.ident = !{!3}

!0 = !{i32 2, !"SDK Version", [2 x i32] [i32 11, i32 3]}
!1 = !{i32 1, !"wchar_size", i32 4}
!2 = !{i32 7, !"PIC Level", i32 2}
!3 = !{!"Homebrew clang version 11.1.0"}
