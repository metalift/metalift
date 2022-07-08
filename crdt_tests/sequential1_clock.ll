; ModuleID = 'sequential1_clock.ll'
source_filename = "sequential1_clock.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

%struct.set = type {}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define %struct.set* @test_init_state() #0 {
bb:
  %i = alloca %struct.set*, align 8
  %i1 = call %struct.set* (...) @set_create()
  store %struct.set* %i1, %struct.set** %i, align 8
  %i2 = load %struct.set*, %struct.set** %i, align 8
  ret %struct.set* %i2
}

declare %struct.set* @set_create(...) #1

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define %struct.set* @test_next_state(%struct.set* %arg, i32 %arg1, i32 %arg2, i32 %arg3) #0 {
bb:
  %i = alloca %struct.set*, align 8
  %i4 = alloca i32, align 4
  %i5 = alloca i32, align 4
  %i6 = alloca i32, align 4
  store %struct.set* %arg, %struct.set** %i, align 8
  store i32 %arg1, i32* %i4, align 4
  store i32 %arg2, i32* %i5, align 4
  store i32 %arg3, i32* %i6, align 4
  %i7 = load i32, i32* %i4, align 4
  %i8 = icmp eq i32 %i7, 1
  br i1 %i8, label %bb19, label %bb20

bb9:                                              ; preds = %bb19
  %i10 = load %struct.set*, %struct.set** %i, align 8
  %i11 = load i32, i32* %i5, align 4
  %i12 = call %struct.set* @set_add(%struct.set* %i10, i32 %i11)
  store %struct.set* %i12, %struct.set** %i, align 8
  br label %bb17

bb13:                                             ; preds = %bb20
  %i14 = load %struct.set*, %struct.set** %i, align 8
  %i15 = load i32, i32* %i5, align 4
  %i16 = call %struct.set* @set_remove(%struct.set* %i14, i32 %i15)
  store %struct.set* %i16, %struct.set** %i, align 8
  br label %bb17

bb17:                                             ; preds = %bb13, %bb9
  %i18 = load %struct.set*, %struct.set** %i, align 8
  ret %struct.set* %i18

bb19:                                             ; preds = %bb
  br label %bb9

bb20:                                             ; preds = %bb
  br label %bb13
}

declare %struct.set* @set_add(%struct.set*, i32) #1

declare %struct.set* @set_remove(%struct.set*, i32) #1

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define i32 @test_response(%struct.set* %arg, i32 %arg1) #0 {
bb:
  %i = alloca %struct.set*, align 8
  %i2 = alloca i32, align 4
  store %struct.set* %arg, %struct.set** %i, align 8
  store i32 %arg1, i32* %i2, align 4
  %i3 = load %struct.set*, %struct.set** %i, align 8
  %i4 = load i32, i32* %i2, align 4
  %i5 = call i32 @set_contains(%struct.set* %i3, i32 %i4)
  ret i32 %i5
}

declare i32 @set_contains(%struct.set*, i32) #1

attributes #0 = { noinline nounwind optnone sspstrong uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="4" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="4" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }

!llvm.module.flags = !{!0, !1}
!llvm.ident = !{!2}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 7, !"PIC Level", i32 2}
!2 = !{!"clang version 11.1.0"}
