#include <tuple>
template <typename...T>
struct tup
{
	std::tuple<T...> contents;
};
template <typename...T>
using Tuple = tup<T...> *;

template <class...T>
Tuple<T...> newTuple() 
{
  
  return new tup<T...>();
}
template <class...T>
Tuple<T...> mktuple(T...args) 
{
  Tuple<T...> r = newTuple<T...>();
  r->contents = std::make_tuple(args...);
  return r;
}

template <class...T>
static auto tupleGet(Tuple<T...> t, int i) 
{ 

	switch (i) {
        case 0: return get<0>(t->contents);
        case 1: return get<1>(t->contents);
    }
}


