package com.trung;


import java.util.ArrayList;
import java.util.HashMap;
import java.util.concurrent.atomic.AtomicReference;

public class Test
{
    public static void main(String[] args)
    {
        var mt = (ArrayList<ArrayList<Number>>) Utilities.toArrayList(new Integer[][]
                {{1,2},{3,4}}

        );
        var outs=new HashMap<String,Object>();
        MathUtilities.makeDiagonalMatrix(mt,outs);
        System.out.println(mt);
        System.out.println(outs);
//        var vector=(ArrayList<Number>)Utilities.toArrayList(new Integer[]{2,3});
//        System.out.println(
//                MathUtilities.solveLinearEquations(mt,vector)
//        );
    }
}
