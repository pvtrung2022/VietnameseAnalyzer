package com.trung;

import com.wolfram.jlink.Expr;

import java.util.Stack;

/**
 * lớp này dùng để thay thế cho sự không ổn định của LoopbackLink trong jlink
 */
public class LoopbackLink
{
    private Stack<StackElement> stack = new Stack<>();

    public void clear()
    {
        this.stack.clear();
    }

    public Expr getExpr()
    {
        var res = new Stack<Expr>();
        while (!this.stack.isEmpty())
        {
            var topEle = this.stack.pop();
            if (!topEle.isFunction)
                res.add(topEle.Expr);
            else
            {
                var arity = topEle.arity;
                var args = new Expr[arity];
                for (var i = 0; i <= arity - 1; i++)
                    args[i] = res.pop();
                var newEle = new Expr(topEle.Expr, args);
                res.push(newEle);
            }
        }
        if (res.size() == 0)
            throw new RuntimeException("Invalid input");
        else if (res.size() == 1)
            return res.pop();
        else
        {
            var size = res.size();
            var args = new Expr[size];
            for (var i = 0; i <= size - 1; i++)
                args[i] = res.pop();
            var seq = new Expr(Expr.SYMBOL, "Sequence");
            return new Expr(seq, args);
        }
    }

    public void putFunction(String head, int arity)
    {
        if (arity < 0)
            throw new RuntimeException("Invalid arity");
        var ele = new StackElement();
        ele.Expr = new Expr(Expr.SYMBOL, head);
        ele.isFunction = true;
        ele.arity = arity;
        stack.push(ele);
    }

    public void put(long value)
    {
        this.put(new Expr(value));
    }

    public void put(int value)
    {
        this.put(new Expr(value));
    }

    public void putSymbol(String value)
    {
        this.put(new Expr(Expr.SYMBOL, value));
    }

    public void put(String value)
    {
        this.put(new Expr(value));
    }

    public void put(double value)
    {
        this.put(new Expr(value));
    }

    public void put(Expr expr)
    {
        var ele = new StackElement();
        ele.Expr = expr;
        stack.push(ele);
    }
}

class StackElement
{
    public Expr Expr;
    public boolean isFunction = false;
    public int arity = -1;
}
