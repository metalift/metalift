; ModuleID = 'domino/programs/hull.ll'
source_filename = "domino/programs/hull.c"
target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx11.0.0"

; Function Attrs: noinline nounwind optnone ssp uwtable
define i32 @test(i32 %arg, i32 %arg1, i32 %arg2, i32 %arg3, i32 %arg4, i32 %arg5, i32 %arg6) #0 {
bb:
  %i = alloca i32, align 4
  %i7 = alloca i32, align 4
  %i8 = alloca i32, align 4
  %i9 = alloca i32, align 4
  %i10 = alloca i32, align 4
  %i11 = alloca i32, align 4
  %i12 = alloca i32, align 4
  %i13 = alloca i32, align 4
  store i32 %arg, i32* %i, align 4
  store i32 %arg1, i32* %i7, align 4
  store i32 %arg2, i32* %i8, align 4
  store i32 %arg3, i32* %i9, align 4
  store i32 %arg4, i32* %i10, align 4
  store i32 %arg5, i32* %i11, align 4
  store i32 %arg6, i32* %i12, align 4
  %i14 = load i32, i32* %i9, align 4
  store i32 %i14, i32* %i7, align 4
  store i32 0, i32* %i13, align 4
  %i15 = load i32, i32* %i8, align 4
  %i16 = load i32, i32* %i10, align 4
  %i17 = add nsw i32 %i15, %i16
  %i18 = load i32, i32* %i9, align 4
  %i19 = add nsw i32 %i17, %i18
  %i20 = load i32, i32* %i, align 4
  %i21 = add nsw i32 %i19, %i20
  %i22 = load i32, i32* %i7, align 4
  %i23 = add nsw i32 %i21, %i22
  store i32 %i23, i32* %i13, align 4
  %i24 = load i32, i32* %i13, align 4
  ret i32 %i24
}

attributes #0 = { noinline nounwind optnone ssp uwtable "frame-pointer"="all" "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+cx8,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "tune-cpu"="generic" }

!llvm.module.flags = !{!0, !1, !2, !3}
!llvm.ident = !{!4}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 7, !"PIC Level", i32 2}
!2 = !{i32 7, !"uwtable", i32 1}
!3 = !{i32 7, !"frame-pointer", i32 2}
!4 = !{!"Homebrew clang version 13.0.0"}
