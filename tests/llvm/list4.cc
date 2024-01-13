// running example from QBS paper

#include "list.h"
#include <iostream>

struct User { int id; int roleId; };
struct Role { int roleId; int name; };

List<User> test(List<User> users, List<Role> roles)
{
  List<User> listUsers = newList<User>();

  for (int i = 0; i < listLength(users); ++i) {
    for (int j = 0; j < listLength(roles); ++j) {
      if (listGet(users, i).roleId == listGet(roles, j).roleId) {
        //std::cout << "add user: " << listGet(users, i).id << " r: " << listGet(users, i).roleId << "\n";
        listUsers = listAppend(listUsers, listGet(users, i));
      }
    }
  }

  return listUsers;
}

// test code
int main (int argc, char ** argv)
{
  List<User> users = newList<User>();
  User u1; u1.id = 1; u1.roleId = 1;
  User u2; u2.id = 2; u2.roleId = 1;
  User u3; u3.id = 3; u3.roleId = 3;
  users = listAppend(users, u1);
  users = listAppend(users, u2);
  users = listAppend(users, u3);

  List<Role> roles = newList<Role>();
  Role r1; r1.roleId = 1; r1.name = 1;
  Role r2; r2.roleId = 2; r2.name = 2;
  roles = listAppend(roles, r1);
  roles = listAppend(roles, r2);

  List<User> r = test(users, roles);
  for (std::vector<User>::const_iterator i = r->contents.begin(); i != r->contents.end(); ++i)
    std::cout << "id: " << i->id << " roleId: " << i->roleId << std::endl;

  return 0;

}
