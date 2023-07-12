; ModuleID = 'no_loop_matmul.ll'
source_filename = "no_loop_matmul.cc"
target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx12.0.0"

; Function Attrs: noinline nounwind optnone ssp uwtable
define i32 @test(i32 %arg, i32 %arg1, i32 %arg2, i32 %arg3, i32 %arg4, i32 %arg5) #0 {
bb:
  %i = alloca i32, align 4
  %i6 = alloca i32, align 4
  %i7 = alloca i32, align 4
  %i8 = alloca i32, align 4
  %i9 = alloca i32, align 4
  %i10 = alloca i32, align 4
  %i11 = alloca i32, align 4
  %i12 = alloca i32, align 4
  store i32 %arg, i32* %i, align 4
  store i32 %arg1, i32* %i6, align 4
  store i32 %arg2, i32* %i7, align 4
  store i32 %arg3, i32* %i8, align 4
  store i32 %arg4, i32* %i9, align 4
  store i32 %arg5, i32* %i10, align 4
  %i13 = load i32, i32* %i, align 4
  %i14 = load i32, i32* %i9, align 4
  %i15 = mul nsw i32 %i13, %i14
  %i16 = load i32, i32* %i7, align 4
  %i17 = load i32, i32* %i10, align 4
  %i18 = mul nsw i32 %i16, %i17
  %i19 = add nsw i32 %i15, %i18
  store i32 %i19, i32* %i11, align 4
  %i20 = load i32, i32* %i6, align 4
  %i21 = load i32, i32* %i9, align 4
  %i22 = mul nsw i32 %i20, %i21
  %i23 = load i32, i32* %i8, align 4
  %i24 = load i32, i32* %i10, align 4
  %i25 = mul nsw i32 %i23, %i24
  %i26 = add nsw i32 %i22, %i25
  store i32 %i26, i32* %i12, align 4
  %i27 = load i32, i32* %i11, align 4
  %i28 = icmp slt i32 %i27, 0
  br i1 %i28, label %bb42, label %bb43

bb29:                                             ; preds = %bb42
  %i30 = load i32, i32* %i11, align 4
  %i31 = sub nsw i32 0, %i30
  store i32 %i31, i32* %i11, align 4
  br label %bb32

bb32:                                             ; preds = %bb43, %bb29
  %i33 = load i32, i32* %i12, align 4
  %i34 = icmp slt i32 %i33, 0
  br i1 %i34, label %bb44, label %bb45

bb35:                                             ; preds = %bb44
  %i36 = load i32, i32* %i12, align 4
  %i37 = sub nsw i32 0, %i36
  store i32 %i37, i32* %i12, align 4
  br label %bb38

bb38:                                             ; preds = %bb45, %bb35
  %i39 = load i32, i32* %i11, align 4
  %i40 = load i32, i32* %i12, align 4
  %i41 = add nsw i32 %i39, %i40
  ret i32 %i41

bb42:                                             ; preds = %bb
  br label %bb29

bb43:                                             ; preds = %bb
  br label %bb32

bb44:                                             ; preds = %bb32
  br label %bb35

bb45:                                             ; preds = %bb32
  br label %bb38
}

attributes #0 = { noinline nounwind optnone ssp uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+cx8,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }

!llvm.module.flags = !{!0, !1}
!llvm.ident = !{!2}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 7, !"PIC Level", i32 2}
!2 = !{!"Homebrew clang version 11.1.0"}
