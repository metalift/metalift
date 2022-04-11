#include <cstdarg>
#include <vector>

template <typename T>
struct list {
    std::vector<T> contents;
};

template <typename T>
using List = list<T> *;

template <class T>
int listLength(List<T> l) {
    return l->contents.size();
}

template <class T>
List<T> newList() {
    // return (List<T>)malloc(sizeof(struct list));
    return new list<T>();
}

template <class T>
T listGet(List<T> l, int i) {
    return l->contents[i];
}

template <class T>
List<T> listAppend(List<T> in, T e) {
    List<T> r = newList<T>();
    for (int i = 0; i < listLength(in); ++i)
        r->contents.push_back(listGet(in, i));
    r->contents.push_back(e);
    return r;
}

template <class T>
List<T> listConcat(List<T> in, List<T> e) {
    List<T> r = newList<T>();
    for (int i = 0; i < listLength(in); ++i)
        r->contents.push_back(listGet(in, i));
    for (int i = 0; i < listLength(e); ++i)
        r->contents.push_back(listGet(e, i));
    return r;
}

template <typename T>
List<T> newListOfReverse(T first) {
    List<T> ret = new list<T>();
    ret = listAppend(ret, first);
    return ret;
}

/** Create list of provided arguments (variable number) in reverse order */
template <typename T, typename... Args>
List<T> newListOfReverse(T first, Args... args) {
    return listAppend(newListOfReverse(args...), first);
}

template <typename T>
List<T> newListOf(T first) {
    return listAppend(newList<T>(), first);
}

template <typename T>
List<T> newListOf(T first, T second) {
    return listAppend(listAppend(newList<T>(), first), second);
}

template <typename T>
List<T> newListOf(T first, T second, T third) {
    return listAppend(listAppend(listAppend(newList<T>(), first), second),
                      third);
}
