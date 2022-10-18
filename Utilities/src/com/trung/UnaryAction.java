package com.trung;

@FunctionalInterface
public interface UnaryAction<S>
{
    public void apply(S s);
}
