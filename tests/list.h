#include <vector>
#include <cstdarg>

template <typename T>
struct list
{
  std::vector<T> contents;
};

template <typename T>
using List = list<T> *;


template <class T>
int listLength (List<T> l)
{
  return l->contents.size();
}

template <class T>
List<T> newList()
{
  //return (List<T>)malloc(sizeof(struct list));
  return new list<T>();
}

template <class T>
List<T> newListOf(int len, T args...) {
  List<T> ret = new list<T>();
  std::va_list args;

  va_start(args, count);
  for (int i = 0; i < count; ++i)
  {
    ret = listAppend(ret, va_arg(args, T));
  }
  va_end(args);

  return ret;
}

template <class T>
T listGet (List<T> l, int i)
{
  return l->contents[i];
}


template <class T>
List<T> listAppend (List<T> in, T e)
{
  List<T> r = newList<T>();
  for (int i = 0; i < listLength(in); ++i)
    r->contents.push_back(listGet(in, i));
  r->contents.push_back(e);
  return r;
}

template <class T>
List<T> listConcat (List<T> in, List<T> e)
{
  List<T> r = newList<T>();
  for (int i = 0; i < listLength(in); ++i)
    r->contents.push_back(listGet(in, i));
  for (int i = 0; i < listLength(e); ++i)
    r->contents.push_back(listGet(e, i));
  return r;
}




