; ModuleID = 'set1.ll'
source_filename = "set1.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

%struct.set = type {}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define %struct.set* @test(i32 %arg) #0 {
bb:
  %tmp = alloca i32, align 4
  %tmp1 = alloca %struct.set*, align 8
  store i32 %arg, i32* %tmp, align 4
  %tmp2 = call %struct.set* (...) @set_create()
  store %struct.set* %tmp2, %struct.set** %tmp1, align 8
  %tmp3 = load %struct.set*, %struct.set** %tmp1, align 8
  %tmp4 = call %struct.set* @set_add(%struct.set* %tmp3, i32 1)
  store %struct.set* %tmp4, %struct.set** %tmp1, align 8
  %tmp5 = load %struct.set*, %struct.set** %tmp1, align 8
  %tmp6 = call %struct.set* @set_add(%struct.set* %tmp5, i32 2)
  store %struct.set* %tmp6, %struct.set** %tmp1, align 8
  %tmp7 = load %struct.set*, %struct.set** %tmp1, align 8
  %tmp8 = call %struct.set* @set_add(%struct.set* %tmp7, i32 3)
  store %struct.set* %tmp8, %struct.set** %tmp1, align 8
  %tmp9 = load i32, i32* %tmp, align 4
  %tmp10 = icmp eq i32 %tmp9, 1
  br i1 %tmp10, label %bb17, label %bb11

bb11:                                             ; preds = %bb
  %tmp12 = load i32, i32* %tmp, align 4
  %tmp13 = icmp eq i32 %tmp12, 2
  br i1 %tmp13, label %bb17, label %bb14

bb14:                                             ; preds = %bb11
  %tmp15 = load i32, i32* %tmp, align 4
  %tmp16 = icmp eq i32 %tmp15, 3
  br i1 %tmp16, label %bb17, label %bb21

bb17:                                             ; preds = %bb14, %bb11, %bb
  %tmp18 = load %struct.set*, %struct.set** %tmp1, align 8
  %tmp19 = load i32, i32* %tmp, align 4
  %tmp20 = call %struct.set* @set_add(%struct.set* %tmp18, i32 %tmp19)
  store %struct.set* %tmp20, %struct.set** %tmp1, align 8
  br label %bb21

bb21:                                             ; preds = %bb17, %bb14
  %tmp22 = load %struct.set*, %struct.set** %tmp1, align 8
  ret %struct.set* %tmp22
}

declare %struct.set* @set_create(...) #1

declare %struct.set* @set_add(%struct.set*, i32) #1

attributes #0 = { noinline nounwind optnone sspstrong uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="4" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="4" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }

!llvm.module.flags = !{!0, !1}
!llvm.ident = !{!2}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 7, !"PIC Level", i32 2}
!2 = !{!"clang version 10.0.1 "}
