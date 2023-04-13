#include <vector>

template <typename T>
struct nestedlist
{
  std::vector<T> contents;
};

template <typename T>
using nestedList = nestedlist<T> *;


template <class T>
int nestedLength(nestedList<T> l) 
{
  return l->contents.size();
}

template <class T>
nestedList<T> nestednewList() 
{
  //return (List<T>)malloc(sizeof(struct list));
  return new nestedlist<T>();
}

template <class T>
List<T> nestedGet(nestedList<T> l, int i) 
{ 
  return new list<T>();
}


template <class T>
nestedList<T> nestedAppend(nestedList<T> in, List<T> e) 
{
    //hack for now return the input list
    
  return in;
}

template <class T>
nestedList<T> listConcat(nestedList<T> in, nestedList<T> e) 
{
  nestedList<T> r = newList<T>();
  for (int i = 0; i < nestedLength(in); ++i)
    r->contents.push_back(nestedGet(in, i));
  for (int i = 0; i < nestedLength(e); ++i)
    r->contents.push_back(nestedGet(e, i));
  return r;
}




