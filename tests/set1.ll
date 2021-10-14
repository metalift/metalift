; ModuleID = 'set1.ll'
source_filename = "set1.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

%struct.set = type {}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define zeroext i1 @test(i32 %arg) #0 {
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
  %tmp9 = load %struct.set*, %struct.set** %tmp1, align 8
  %tmp10 = load i32, i32* %tmp, align 4
  %tmp11 = call zeroext i1 @set_contains(%struct.set* %tmp9, i32 %tmp10)
  ret i1 %tmp11
}

declare %struct.set* @set_create(...) #1

declare %struct.set* @set_add(%struct.set*, i32) #1

declare zeroext i1 @set_contains(%struct.set*, i32) #1

attributes #0 = { noinline nounwind optnone sspstrong uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="4" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="4" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }

!llvm.module.flags = !{!0, !1}
!llvm.ident = !{!2}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 7, !"PIC Level", i32 2}
!2 = !{!"clang version 10.0.1 "}
