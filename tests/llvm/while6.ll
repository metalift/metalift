; ModuleID = 'while6.ll'
source_filename = "while6.c"
target datalayout = "e-m:o-i64:64-i128:128-n32:64-S128"
target triple = "arm64-apple-macosx11.0.0"

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define i32 @test() #0 {
entry:
  %x = alloca i32, align 4
  %y = alloca i32, align 4
  %z = alloca i32, align 4
  store i32 0, i32* %x, align 4
  store i32 0, i32* %y, align 4
  br label %while.cond

while.cond:                                       ; preds = %while.end, %entry
  %i = load i32, i32* %y, align 4
  %cmp = icmp slt i32 %i, 3
  br i1 %cmp, label %while.body, label %while.end6

while.body:                                       ; preds = %while.cond
  store i32 0, i32* %z, align 4
  br label %while.cond1

while.cond1:                                      ; preds = %while.body3, %while.body
  %i1 = load i32, i32* %z, align 4
  %cmp2 = icmp slt i32 %i1, 5
  br i1 %cmp2, label %while.body3, label %while.end

while.body3:                                      ; preds = %while.cond1
  %i2 = load i32, i32* %x, align 4
  %add = add i32 %i2, 2
  store i32 %add, i32* %x, align 4
  %i3 = load i32, i32* %z, align 4
  %add4 = add i32 %i3, 1
  store i32 %add4, i32* %z, align 4
  br label %while.cond1

while.end:                                        ; preds = %while.cond1
  %i4 = load i32, i32* %y, align 4
  %add5 = add i32 %i4, 1
  store i32 %add5, i32* %y, align 4
  br label %while.cond

while.end6:                                       ; preds = %while.cond
  %i5 = load i32, i32* %x, align 4
  ret i32 %i5
}

attributes #0 = { noinline nounwind optnone sspstrong uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="non-leaf" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="4" "target-cpu"="apple-a13" "target-features"="+aes,+crc,+crypto,+fullfp16,+lse,+neon,+ras,+rcpc,+rdm,+sha2,+v8.3a,+zcm,+zcz" "unsafe-fp-math"="false" "use-soft-float"="false" }

!llvm.module.flags = !{!0, !1}
!llvm.ident = !{!2}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 7, !"PIC Level", i32 2}
!2 = !{!"clang version 11.1.0"}
