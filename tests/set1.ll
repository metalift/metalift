; ModuleID = 'set1.ll'
source_filename = "set1.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

%struct.set = type {}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define %struct.set* @test(%struct.set* %arg, i32 %arg1, i32 %arg2) #0 {
bb:
  %tmp = alloca %struct.set*, align 8
  %tmp3 = alloca i32, align 4
  %tmp4 = alloca i32, align 4
  store %struct.set* %arg, %struct.set** %tmp, align 8
  store i32 %arg1, i32* %tmp3, align 4
  store i32 %arg2, i32* %tmp4, align 4
  %tmp5 = load i32, i32* %tmp3, align 4
  %tmp6 = icmp eq i32 %tmp5, 1
  br i1 %tmp6, label %bb17, label %bb18

bb7:                                              ; preds = %bb17
  %tmp8 = load %struct.set*, %struct.set** %tmp, align 8
  %tmp9 = load i32, i32* %tmp4, align 4
  %tmp10 = call %struct.set* @set_add(%struct.set* %tmp8, i32 %tmp9)
  store %struct.set* %tmp10, %struct.set** %tmp, align 8
  br label %bb15

bb11:                                             ; preds = %bb18
  %tmp12 = load %struct.set*, %struct.set** %tmp, align 8
  %tmp13 = load i32, i32* %tmp4, align 4
  %tmp14 = call %struct.set* @set_remove(%struct.set* %tmp12, i32 %tmp13)
  store %struct.set* %tmp14, %struct.set** %tmp, align 8
  br label %bb15

bb15:                                             ; preds = %bb11, %bb7
  %tmp16 = load %struct.set*, %struct.set** %tmp, align 8
  ret %struct.set* %tmp16

bb17:                                             ; preds = %bb
  br label %bb7

bb18:                                             ; preds = %bb
  br label %bb11
}

declare %struct.set* @set_add(%struct.set*, i32) #1

declare %struct.set* @set_remove(%struct.set*, i32) #1

attributes #0 = { noinline nounwind optnone sspstrong uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="4" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="4" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }

!llvm.module.flags = !{!0, !1}
!llvm.ident = !{!2}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 7, !"PIC Level", i32 2}
!2 = !{!"clang version 10.0.1 "}
