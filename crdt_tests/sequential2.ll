; ModuleID = 'sequential2.ll'
source_filename = "sequential2.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define i32 @test_init_state() #0 {
bb:
  %i = alloca i32, align 4
  store i32 0, i32* %i, align 4
  %i1 = load i32, i32* %i, align 4
  ret i32 %i1
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define i32 @test_next_state(i32 %arg, i32 %arg1, i32 %arg2) #0 {
bb:
  %i = alloca i32, align 4
  %i3 = alloca i32, align 4
  %i4 = alloca i32, align 4
  store i32 %arg, i32* %i, align 4
  store i32 %arg1, i32* %i3, align 4
  store i32 %arg2, i32* %i4, align 4
  %i5 = load i32, i32* %i3, align 4
  %i6 = icmp eq i32 %i5, 1
  br i1 %i6, label %bb15, label %bb16

bb7:                                              ; preds = %bb15
  %i8 = load i32, i32* %i, align 4
  %i9 = add i32 %i8, 1
  store i32 %i9, i32* %i, align 4
  br label %bb13

bb10:                                             ; preds = %bb16
  %i11 = load i32, i32* %i, align 4
  %i12 = sub i32 %i11, 1
  store i32 %i12, i32* %i, align 4
  br label %bb13

bb13:                                             ; preds = %bb10, %bb7
  %i14 = load i32, i32* %i, align 4
  ret i32 %i14

bb15:                                             ; preds = %bb
  br label %bb7

bb16:                                             ; preds = %bb
  br label %bb10
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define i32 @test_response(i32 %arg) #0 {
bb:
  %i = alloca i32, align 4
  store i32 %arg, i32* %i, align 4
  %i1 = load i32, i32* %i, align 4
  ret i32 %i1
}

attributes #0 = { noinline nounwind optnone sspstrong uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="4" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }

!llvm.module.flags = !{!0, !1}
!llvm.ident = !{!2}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 7, !"PIC Level", i32 2}
!2 = !{!"clang version 11.1.0"}
