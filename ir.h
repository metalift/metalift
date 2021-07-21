#ifndef METALIFT_IR_H
#define METALIFT_IR_H

#include <utility>
#include <iostream>

namespace metalift
{
struct Expr 
{
  virtual std::ostream& print(std::ostream &os) const = 0;

  friend std::ostream& operator<<(std::ostream &os, const Expr &e)
  {
    return e.print(os);
  }
};

struct Lit : public Expr
{
  int val;
  Lit(int val) : val(val) {}

  virtual std::ostream& print (std::ostream &os) const override
  {
    os << val;
    return os;
  }
};

struct Var : public Expr
{
  const std::string name;
  Var(const std::string name) : name(name) {}
  virtual std::ostream& print (std::ostream &os) const override
  {
    os << name;
    return os;
  }
};


struct Unary : public Expr 
{
  Expr * e;
  Unary(Expr * e) : e(std::move(e)) {}
};

struct Assume : public Unary
{
  Assume(Expr * e) : Unary(e) {}
  virtual std::ostream& print (std::ostream &os) const override
  {
    os << "(=> " << *e << ")";
    return os;
  }
};

struct Assert : public Unary
{
  Assert(Expr * e) : Unary(e) {}
  virtual std::ostream& print (std::ostream &os) const override
  {
    os << "(assert " << *e << ")";
    return os;
  }
};


struct Binary : public Expr
{
  Expr * left;
  Expr * right;
  Binary(Expr * l, Expr * r) : left(std::move(l)), right(std::move(r)) {}
};

struct Assign : public Binary
{
  Assign(Expr * l, Expr * r) : Binary(l, r) {}
  friend std::ostream& operator<<(std::ostream& os, const Assign &a);
  virtual std::ostream& print (std::ostream &os) const override
  {
    os << "(= " << *left << " " << *right << ")";
    return os;
  }
};

struct Add : public Binary
{
  Add(Expr * l, Expr * r) : Binary(l, r) {}
  virtual std::ostream& print (std::ostream &os) const override
  {
    os << "(+ " << *left << " " << *right << ")";
    return os;
  }
};

struct And : public Binary
{
  And(Expr * l, Expr * r) : Binary(l, r) {}
  virtual std::ostream& print (std::ostream &os) const override
  {
    os << "(and " << *left << " " << *right << ")";
    return os;
  }
};

struct Leq : public Binary
{
  Leq(Expr * l, Expr * r) : Binary(l, r) {}
  virtual std::ostream& print (std::ostream &os) const override
  {
    os << "(<= " << *left << " " << *right << ")";
    return os;
  }
};

struct Ite : public Expr
{
  Expr * cond;
  Expr * conseq;
  Expr * alt;
  Ite(Expr * cond, Expr * conseq, Expr * alt) : cond(cond), conseq(conseq), alt(alt) {}
  virtual std::ostream& print (std::ostream &os) const override
  {
    os << "(ite " << *cond << " " << *conseq << " " << *alt << ")";
    return os;
  }
};

};

#endif