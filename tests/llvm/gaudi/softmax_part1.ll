; ModuleID = 'gaudi/softmax_part1.ll'
source_filename = "gaudi/softmax_part1.cc"
target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx12.0.0"

%"class.std::__1::vector" = type { %"class.std::__1::__vector_base" }
%"class.std::__1::__vector_base" = type { i32*, i32*, %"class.std::__1::__compressed_pair" }
%"class.std::__1::__compressed_pair" = type { %"struct.std::__1::__compressed_pair_elem" }
%"struct.std::__1::__compressed_pair_elem" = type { i32* }

; Function Attrs: noinline nounwind optnone ssp uwtable
define i32 @_Z13softmax_part1NSt3__16vectorIiNS_9allocatorIiEEEEi(%"class.std::__1::vector"* %input, i32 %max_pos) #0 {
entry:
  %max_pos.addr = alloca i32, align 4
  %max_val = alloca i32, align 4
  %i = alloca i32, align 4
  store i32 %max_pos, i32* %max_pos.addr, align 4
  %call = call nonnull align 4 dereferenceable(4) i32* @_ZNSt3__16vectorIiNS_9allocatorIiEEEixEm(%"class.std::__1::vector"* %input, i64 0) #1
  %i1 = load i32, i32* %call, align 4
  store i32 %i1, i32* %max_val, align 4
  store i32 1, i32* %i, align 4
  br label %for.cond

for.cond:                                         ; preds = %for.inc, %entry
  %i2 = load i32, i32* %i, align 4
  %i3 = load i32, i32* %max_pos.addr, align 4
  %cmp = icmp slt i32 %i2, %i3
  br i1 %cmp, label %for.body, label %for.end

for.body:                                         ; preds = %for.cond
  %i4 = load i32, i32* %i, align 4
  %conv = sext i32 %i4 to i64
  %call1 = call nonnull align 4 dereferenceable(4) i32* @_ZNSt3__16vectorIiNS_9allocatorIiEEEixEm(%"class.std::__1::vector"* %input, i64 %conv) #1
  %i5 = load i32, i32* %call1, align 4
  %i6 = load i32, i32* %max_val, align 4
  %cmp2 = icmp sgt i32 %i5, %i6
  br i1 %cmp2, label %if.then, label %if.end

if.then:                                          ; preds = %for.body
  %i7 = load i32, i32* %i, align 4
  %conv3 = sext i32 %i7 to i64
  %call4 = call nonnull align 4 dereferenceable(4) i32* @_ZNSt3__16vectorIiNS_9allocatorIiEEEixEm(%"class.std::__1::vector"* %input, i64 %conv3) #1
  %i8 = load i32, i32* %call4, align 4
  store i32 %i8, i32* %max_val, align 4
  br label %if.end

if.end:                                           ; preds = %if.then, %for.body
  br label %for.inc

for.inc:                                          ; preds = %if.end
  %i9 = load i32, i32* %i, align 4
  %inc = add nsw i32 %i9, 1
  store i32 %inc, i32* %i, align 4
  br label %for.cond

for.end:                                          ; preds = %for.cond
  %i10 = load i32, i32* %max_val, align 4
  ret i32 %i10
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define linkonce_odr hidden nonnull align 4 dereferenceable(4) i32* @_ZNSt3__16vectorIiNS_9allocatorIiEEEixEm(%"class.std::__1::vector"* %this, i64 %__n) #0 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::vector"*, align 8
  %__n.addr = alloca i64, align 8
  store %"class.std::__1::vector"* %this, %"class.std::__1::vector"** %this.addr, align 8
  store i64 %__n, i64* %__n.addr, align 8
  %this1 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %this.addr, align 8
  %i = bitcast %"class.std::__1::vector"* %this1 to %"class.std::__1::__vector_base"*
  %__begin_ = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %i, i32 0, i32 0
  %i1 = load i32*, i32** %__begin_, align 8
  %i2 = load i64, i64* %__n.addr, align 8
  %arrayidx = getelementptr inbounds i32, i32* %i1, i64 %i2
  ret i32* %arrayidx
}

attributes #0 = { noinline nounwind optnone ssp uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+cx8,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { nounwind }

!llvm.module.flags = !{!0, !1}
!llvm.ident = !{!2}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 7, !"PIC Level", i32 2}
!2 = !{!"Homebrew clang version 11.1.0"}
