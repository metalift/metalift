; ModuleID = 'tests/domino/programs/hull.ll'
source_filename = "tests/domino/programs/hull.c"
target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx11.0.0"

; Function Attrs: noinline nounwind optnone ssp uwtable
define i32 @test(i32 %arg, i32 %arg1, i32 %arg2, i32 %arg3, i32 %arg4) #0 {
bb:
  %i = alloca i32, align 4
  %i5 = alloca i32, align 4
  %i6 = alloca i32, align 4
  %i7 = alloca i32, align 4
  %i8 = alloca i32, align 4
  store i32 %arg, i32* %i, align 4
  store i32 %arg1, i32* %i5, align 4
  store i32 %arg2, i32* %i6, align 4
  store i32 %arg3, i32* %i7, align 4
  store i32 %arg4, i32* %i8, align 4
  %i9 = load i32, i32* %i7, align 4
  store i32 %i9, i32* %i5, align 4
  %i10 = load i32, i32* %i6, align 4
  %i11 = load i32, i32* %i8, align 4
  %i12 = add nsw i32 %i10, %i11
  %i13 = load i32, i32* %i7, align 4
  %i14 = add nsw i32 %i12, %i13
  %i15 = load i32, i32* %i, align 4
  %i16 = add nsw i32 %i14, %i15
  %i17 = load i32, i32* %i5, align 4
  %i18 = add nsw i32 %i16, %i17
  ret i32 %i18
}

attributes #0 = { noinline nounwind optnone ssp uwtable "frame-pointer"="all" "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+cx8,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "tune-cpu"="generic" }

!llvm.module.flags = !{!0, !1, !2, !3}
!llvm.ident = !{!4}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 7, !"PIC Level", i32 2}
!2 = !{i32 7, !"uwtable", i32 1}
!3 = !{i32 7, !"frame-pointer", i32 2}
!4 = !{!"Homebrew clang version 13.0.0"}
