; ModuleID = 'no_loop_matmul.ll'
source_filename = "no_loop_matmul.cc"
target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx12.0.0"

; Function Attrs: noinline nounwind optnone ssp uwtable
define i32 @test(i32 %a0, i32 %a1, i32 %b0, i32 %b1, i32 %x0, i32 %x1) #0 {
entry:
  %a0.addr = alloca i32, align 4
  %a1.addr = alloca i32, align 4
  %b0.addr = alloca i32, align 4
  %b1.addr = alloca i32, align 4
  %x0.addr = alloca i32, align 4
  %x1.addr = alloca i32, align 4
  %p0 = alloca i32, align 4
  %p1 = alloca i32, align 4
  store i32 %a0, i32* %a0.addr, align 4
  store i32 %a1, i32* %a1.addr, align 4
  store i32 %b0, i32* %b0.addr, align 4
  store i32 %b1, i32* %b1.addr, align 4
  store i32 %x0, i32* %x0.addr, align 4
  store i32 %x1, i32* %x1.addr, align 4
  %i = load i32, i32* %a0.addr, align 4
  %i1 = load i32, i32* %x0.addr, align 4
  %mul = mul nsw i32 %i, %i1
  %i2 = load i32, i32* %b0.addr, align 4
  %i3 = load i32, i32* %x1.addr, align 4
  %mul1 = mul nsw i32 %i2, %i3
  %add = add nsw i32 %mul, %mul1
  store i32 %add, i32* %p0, align 4
  %i4 = load i32, i32* %a1.addr, align 4
  %i5 = load i32, i32* %x0.addr, align 4
  %mul2 = mul nsw i32 %i4, %i5
  %i6 = load i32, i32* %b1.addr, align 4
  %i7 = load i32, i32* %x1.addr, align 4
  %mul3 = mul nsw i32 %i6, %i7
  %add4 = add nsw i32 %mul2, %mul3
  store i32 %add4, i32* %p1, align 4
  %i8 = load i32, i32* %p0, align 4
  %cmp = icmp slt i32 %i8, 0
  br i1 %cmp, label %bb, label %bb14

if.then:                                          ; preds = %bb
  %i9 = load i32, i32* %p0, align 4
  %sub = sub nsw i32 0, %i9
  store i32 %sub, i32* %p0, align 4
  br label %if.end

if.end:                                           ; preds = %bb14, %if.then
  %i10 = load i32, i32* %p1, align 4
  %cmp5 = icmp slt i32 %i10, 0
  br i1 %cmp5, label %bb15, label %bb16

if.then6:                                         ; preds = %bb15
  %i11 = load i32, i32* %p1, align 4
  %sub7 = sub nsw i32 0, %i11
  store i32 %sub7, i32* %p1, align 4
  br label %if.end8

if.end8:                                          ; preds = %bb16, %if.then6
  %i12 = load i32, i32* %p0, align 4
  %i13 = load i32, i32* %p1, align 4
  %add9 = add nsw i32 %i12, %i13
  ret i32 %add9

bb:                                               ; preds = %entry
  br label %if.then

bb14:                                             ; preds = %entry
  br label %if.end

bb15:                                             ; preds = %if.end
  br label %if.then6

bb16:                                             ; preds = %if.end
  br label %if.end8
}

attributes #0 = { noinline nounwind optnone ssp uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+cx8,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }

!llvm.module.flags = !{!0, !1}
!llvm.ident = !{!2}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 7, !"PIC Level", i32 2}
!2 = !{!"Homebrew clang version 11.1.0"}
