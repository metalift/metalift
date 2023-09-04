; ModuleID = 'list_abs_sum.ll'
source_filename = "list_abs_sum.cc"
target datalayout = "e-m:o-i64:64-i128:128-n32:64-S128"
target triple = "arm64-apple-macosx11.0.0"

%struct.list = type { %"class.std::__1::vector" }
%"class.std::__1::vector" = type { %"class.std::__1::__vector_base" }
%"class.std::__1::__vector_base" = type { i32*, i32*, %"class.std::__1::__compressed_pair" }
%"class.std::__1::__compressed_pair" = type { %"struct.std::__1::__compressed_pair_elem" }
%"struct.std::__1::__compressed_pair_elem" = type { i32* }

; Function Attrs: noinline optnone sspstrong uwtable
define i32 @test(%struct.list* %lst) #0 {
entry:
  %lst.addr = alloca %struct.list*, align 8
  %sum = alloca i32, align 4
  %i = alloca i32, align 4
  %curr_el = alloca i32, align 4
  store %struct.list* %lst, %struct.list** %lst.addr, align 8
  store i32 0, i32* %sum, align 4
  store i32 0, i32* %i, align 4
  br label %for.cond

for.cond:                                         ; preds = %for.inc, %entry
  %i1 = load i32, i32* %i, align 4
  %i2 = load %struct.list*, %struct.list** %lst.addr, align 8
  %call = call i32 @_Z10listLengthIiEiP4listIT_E(%struct.list* %i2)
  %cmp = icmp slt i32 %i1, %call
  br i1 %cmp, label %bb, label %bb12

for.body:                                         ; preds = %bb
  %i3 = load %struct.list*, %struct.list** %lst.addr, align 8
  %i4 = load i32, i32* %i, align 4
  %call1 = call i32 @_Z7listGetIiET_P4listIS0_Ei(%struct.list* %i3, i32 %i4)
  store i32 %call1, i32* %curr_el, align 4
  %i5 = load i32, i32* %curr_el, align 4
  %cmp2 = icmp slt i32 %i5, 0
  br i1 %cmp2, label %bb13, label %bb14

if.then:                                          ; preds = %bb13
  %i6 = load i32, i32* %curr_el, align 4
  %sub = sub i32 0, %i6
  %i7 = load i32, i32* %sum, align 4
  %add = add i32 %i7, %sub
  store i32 %add, i32* %sum, align 4
  br label %if.end

if.else:                                          ; preds = %bb14
  %i8 = load i32, i32* %curr_el, align 4
  %i9 = load i32, i32* %sum, align 4
  %add3 = add i32 %i9, %i8
  store i32 %add3, i32* %sum, align 4
  br label %if.end

if.end:                                           ; preds = %if.else, %if.then
  br label %for.inc

for.inc:                                          ; preds = %if.end
  %i10 = load i32, i32* %i, align 4
  %inc = add i32 %i10, 1
  store i32 %inc, i32* %i, align 4
  br label %for.cond

for.end:                                          ; preds = %bb12
  %i11 = load i32, i32* %sum, align 4
  ret i32 %i11

bb:                                               ; preds = %for.cond
  br label %for.body

bb12:                                             ; preds = %for.cond
  br label %for.end

bb13:                                             ; preds = %for.body
  br label %if.then

bb14:                                             ; preds = %for.body
  br label %if.else
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr i32 @_Z10listLengthIiEiP4listIT_E(%struct.list* %l) #1 {
entry:
  %l.addr = alloca %struct.list*, align 8
  store %struct.list* %l, %struct.list** %l.addr, align 8
  %i = load %struct.list*, %struct.list** %l.addr, align 8
  %contents = getelementptr inbounds %struct.list, %struct.list* %i, i32 0, i32 0
  %call = call i64 @_ZNKSt3__16vectorIiNS_9allocatorIiEEE4sizeEv(%"class.std::__1::vector"* %contents) #2
  %conv = trunc i64 %call to i32
  ret i32 %conv
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr i32 @_Z7listGetIiET_P4listIS0_Ei(%struct.list* %l, i32 %i) #1 {
entry:
  %l.addr = alloca %struct.list*, align 8
  %i.addr = alloca i32, align 4
  store %struct.list* %l, %struct.list** %l.addr, align 8
  store i32 %i, i32* %i.addr, align 4
  %i1 = load %struct.list*, %struct.list** %l.addr, align 8
  %contents = getelementptr inbounds %struct.list, %struct.list* %i1, i32 0, i32 0
  %i2 = load i32, i32* %i.addr, align 4
  %conv = sext i32 %i2 to i64
  %call = call nonnull align 4 dereferenceable(4) i32* @_ZNSt3__16vectorIiNS_9allocatorIiEEEixEm(%"class.std::__1::vector"* %contents, i64 %conv) #2
  %i3 = load i32, i32* %call, align 4
  ret i32 %i3
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden i64 @_ZNKSt3__16vectorIiNS_9allocatorIiEEE4sizeEv(%"class.std::__1::vector"* %this) #1 align 2 {
entry:
  %this.addr = alloca %"class.std::__1::vector"*, align 8
  store %"class.std::__1::vector"* %this, %"class.std::__1::vector"** %this.addr, align 8
  %this1 = load %"class.std::__1::vector"*, %"class.std::__1::vector"** %this.addr, align 8
  %i = bitcast %"class.std::__1::vector"* %this1 to %"class.std::__1::__vector_base"*
  %__end_ = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %i, i32 0, i32 1
  %i1 = load i32*, i32** %__end_, align 8
  %i2 = bitcast %"class.std::__1::vector"* %this1 to %"class.std::__1::__vector_base"*
  %__begin_ = getelementptr inbounds %"class.std::__1::__vector_base", %"class.std::__1::__vector_base"* %i2, i32 0, i32 0
  %i3 = load i32*, i32** %__begin_, align 8
  %sub.ptr.lhs.cast = ptrtoint i32* %i1 to i64
  %sub.ptr.rhs.cast = ptrtoint i32* %i3 to i64
  %sub.ptr.sub = sub i64 %sub.ptr.lhs.cast, %sub.ptr.rhs.cast
  %sub.ptr.div = sdiv exact i64 %sub.ptr.sub, 4
  ret i64 %sub.ptr.div
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define linkonce_odr hidden nonnull align 4 dereferenceable(4) i32* @_ZNSt3__16vectorIiNS_9allocatorIiEEEixEm(%"class.std::__1::vector"* %this, i64 %__n) #1 align 2 {
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
  %arrayidx = getelementptr i32, i32* %i1, i64 %i2
  ret i32* %arrayidx
}

attributes #0 = { noinline optnone sspstrong uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="non-leaf" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="4" "target-cpu"="apple-a13" "target-features"="+aes,+crc,+crypto,+fullfp16,+lse,+neon,+ras,+rcpc,+rdm,+sha2,+v8.3a,+zcm,+zcz" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { noinline nounwind optnone sspstrong uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="non-leaf" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="4" "target-cpu"="apple-a13" "target-features"="+aes,+crc,+crypto,+fullfp16,+lse,+neon,+ras,+rcpc,+rdm,+sha2,+v8.3a,+zcm,+zcz" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #2 = { nounwind }

!llvm.module.flags = !{!0, !1}
!llvm.ident = !{!2}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 7, !"PIC Level", i32 2}
!2 = !{!"clang version 11.1.0"}
