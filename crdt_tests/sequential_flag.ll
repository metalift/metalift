; ModuleID = 'sequential_flag.ll'
source_filename = "sequential_flag.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define i32 @test_init_state() #0 {
bb:
  ret i32 0
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define i32 @test_next_state(i32 %arg, i32 %arg1, i32 %arg2) #0 {
bb:
  %i = alloca i32, align 4
  %i3 = alloca i32, align 4
  %i4 = alloca i32, align 4
  %i5 = alloca i32, align 4
  store i32 %arg, i32* %i3, align 4
  store i32 %arg1, i32* %i4, align 4
  store i32 %arg2, i32* %i5, align 4
  %i6 = load i32, i32* %i4, align 4
  %i7 = icmp eq i32 %i6, 1
  br i1 %i7, label %bb12, label %bb13

bb8:                                              ; preds = %bb12
  store i32 1, i32* %i, align 4
  br label %bb10

bb9:                                              ; preds = %bb13
  store i32 0, i32* %i, align 4
  br label %bb10

bb10:                                             ; preds = %bb9, %bb8
  %i11 = load i32, i32* %i, align 4
  ret i32 %i11

bb12:                                             ; preds = %bb
  br label %bb8

bb13:                                             ; preds = %bb
  br label %bb9
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
