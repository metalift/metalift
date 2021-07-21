#include <vector>

struct list
{
  std::vector<int> contents;
};

typedef struct list * List;

List newList() 
{
  return (List)malloc(sizeof(struct list));
}

int listLength (List l) 
{
  return l->contents.size();
}

int listGet (List l, int i) 
{ 
  return l->contents[i];
}

List listAppend (List in, int e) 
{
  List r = newList();
  for (int i = 0; i < listLength(in); ++i)
    r->contents.push_back(listGet(in, i));
  r->contents.push_back(e);
  return r;
}


