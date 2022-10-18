package com.trung;

import java.lang.reflect.Array;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.concurrent.atomic.AtomicReference;

public class MathUtilities
{
    public static ArrayList<Double> solveLinearEquations(
            ArrayList<ArrayList<Number>> matrix,
            ArrayList<Number> vector)
    {
        NullFunction<ArrayList<ArrayList<Number>>> copyMatrix = () ->
        {
            return Utilities.map(
                    (ArrayList<Number> row) -> (ArrayList<Number>) row.clone()
                    , matrix);
        };
        var copiedMt0 = copyMatrix.apply();
        var outs0 = new HashMap<String, Object>();
        makeDiagonalMatrix(copiedMt0, outs0);
        var rowDeps = Utilities.makeArrayList((Collection<Integer>) outs0.get("independentRows"));
        if (rowDeps.size() == 0)
            return Utilities.table(i -> 0d, 0, matrix.get(0).size() - 1);
        var copiedMt1 = copyMatrix.apply();
        var outs1 = new HashMap<String, Object>();
        makeDiagonalMatrix(transpose(copiedMt1), outs1);
        var columnDeps = Utilities.makeArrayList((Collection<Integer>) outs1.get("independentRows"));
        var subMatrix = subMatrix(matrix, rowDeps, columnDeps);
        var subVector = Utilities.map(
                (Integer i) ->
                {
                    var aux = new ArrayList<Number>();
                    aux.add(vector.get(i));
                    return aux;
                }
                , rowDeps);
        var sol = matrixProduct(
                (ArrayList<ArrayList<Number>>) (Object) inverseMatrix(subMatrix), subVector
        );
        var mainSol = Utilities.table(
                i ->
                {
                    return 0d;
                }
                , 0, vector.size() - 1
        );
        for (var i = 0; i <= columnDeps.size() - 1; i++)
        {
            var iValue = columnDeps.get(i);
            mainSol.set(iValue,
                    sol.get(i).get(0)
            );
        }
        return mainSol;
    }

    public static ArrayList<ArrayList<Number>> subMatrix(
            ArrayList<ArrayList<Number>> matrix,
            Collection<Integer> rows,
            Collection<Integer> columns)
    {
        var sortedRows = Utilities.makeArrayList(rows);
        var sortedColumns = Utilities.makeArrayList(columns);
        Utilities.sortBy(sortedRows, x -> x);
        Utilities.sortBy(sortedColumns, x -> x);
        var res = Utilities.map(
                (Integer i) -> matrix.get(i)
                , sortedRows);
        return Utilities.map(
                (ArrayList<Number> row) -> Utilities.map((Integer i) -> row.get(i),
                        sortedColumns)
                , res);
    }

    public static ArrayList<Double> leastSquares(ArrayList<ArrayList<Number>> input)
    {
        var Amt = Utilities.map(
                (ArrayList<Number> row) -> Utilities.part(row, 0, row.size() - 2)
                , input);
        var bmt = Utilities.map(
                (ArrayList<Number> row) ->
                {
                    var aux = new ArrayList<Number>();
                    aux.add(Utilities.getLastElement(row));
                    return aux;
                }
                , input
        );
        var mtProd = (ArrayList<ArrayList<Number>>) (Object) matrixProduct(transpose(Amt), Amt);
        var vector = (ArrayList<ArrayList<Number>>) (Object) matrixProduct(transpose(Amt), bmt);
        if (determinant(mtProd) != 0d)
        {
            var res = matrixProduct((ArrayList<ArrayList<Number>>) (Object) inverseMatrix(mtProd),
                    vector);
            return Utilities.map(
                    (ArrayList<Double> x) -> x.get(0)
                    , res);
        } else
        {
            return solveLinearEquations(mtProd,
                    Utilities.map((ArrayList<Number> x) -> x.get(0), vector)
            );
        }
    }


    public static ArrayList<ArrayList<Number>> makeMatrix(int m, int n, BinaryFunction<Integer, Integer, Number> indexf)
    {
        var res = new Number[m][n];
        for (var i = 0; i <= m - 1; i++)
            for (var j = 0; j <= n - 1; j++)
                res[i][j] = indexf.apply(i, j);
        return (ArrayList<ArrayList<Number>>) Utilities.toArrayList(res);
    }

    public static ArrayList<ArrayList<Double>> zeroMatrix(int n)
    {
        return (ArrayList<ArrayList<Double>>) (Object) makeMatrix(n, n,
                (i, j) -> 0d
        );
    }

    public static ArrayList<ArrayList<Double>> identityMatrix(int n)
    {
        return (ArrayList<ArrayList<Double>>) (Object) makeMatrix(n, n,
                (i, j) -> i.equals(j) ? 1d : 0d
        );
    }


    public static ArrayList<ArrayList<Double>> matrixPlus(ArrayList<ArrayList<Number>> matrix0,
                                                          ArrayList<ArrayList<Number>> matrix1,
                                                          ArrayList<ArrayList<Number>> matrix2,
                                                          ArrayList<ArrayList<Number>>... matrices)
    {
        var res = matrixPlus(matrix0, matrix1);
        res = matrixPlus((ArrayList<ArrayList<Number>>) (Object) res, matrix2);
        for (var i = 0; i <= matrices.length - 1; i++)
            res = matrixPlus((ArrayList<ArrayList<Number>>) (Object) res, matrices[i]);
        return res;
    }

    public static ArrayList<ArrayList<Double>> matrixPlus(ArrayList<ArrayList<Number>> matrix0,
                                                          ArrayList<ArrayList<Number>> matrix1)
    {
        var m = matrix0.size();
        var n = matrix0.get(0).size();
        var res = new Double[m][n];
        for (var i = 0; i <= m - 1; i++)
            for (var j = 0; j <= n - 1; j++)
                res[i][j] = matrix0.get(i).get(j).doubleValue() + matrix1.get(i).get(j).doubleValue();
        return (ArrayList<ArrayList<Double>>) Utilities.toArrayList(res);
    }

    public static ArrayList<ArrayList<Double>> matrixProduct(ArrayList<ArrayList<Number>> matrix, Number a)
    {
        return matrixProduct(a, matrix);
    }

    public static ArrayList<ArrayList<Double>> matrixProduct(Number a, ArrayList<ArrayList<Number>> matrix)
    {
        var m = matrix.size();
        var n = matrix.get(0).size();
        var res = new Double[m][n];
        for (var i = 0; i <= m - 1; i++)
            for (var j = 0; j <= n - 1; j++)
                res[i][j] = a.doubleValue() * matrix.get(i).get(j).doubleValue();
        return (ArrayList<ArrayList<Double>>) Utilities.toArrayList(res);
    }

    public static ArrayList<ArrayList<Double>> matrixProduct(ArrayList<ArrayList<Number>> matrix0,
                                                             ArrayList<ArrayList<Number>> matrix1,
                                                             ArrayList<ArrayList<Number>> matrix2,
                                                             ArrayList<ArrayList<Number>>... matrices)
    {
        var res = matrixProduct(matrix0, matrix1);
        res = matrixProduct((ArrayList<ArrayList<Number>>) (Object) res, matrix2);
        for (var i = 0; i <= matrices.length - 1; i++)
            res = matrixProduct((ArrayList<ArrayList<Number>>) (Object) res, matrices[i]);
        return res;
    }

    public static ArrayList<ArrayList<Double>> matrixProduct(ArrayList<ArrayList<Number>> matrix0, ArrayList<ArrayList<Number>> matrix1)
    {
        var m = matrix0.size();
        var n = matrix0.get(0).size();
        var p = matrix1.get(0).size();
        var arr = new Double[m][p];
        for (var i = 0; i <= m - 1; i++)
            for (var j = 0; j <= p - 1; j++)
            {
                arr[i][j] = 0d;
                for (var k = 0; k <= n - 1; k++)
                    arr[i][j] += (matrix0.get(i).get(k).doubleValue()) * (matrix1.get(k).get(j).doubleValue());
            }
        return (ArrayList<ArrayList<Double>>) Utilities.toArrayList(arr);
    }

    public static ArrayList<ArrayList<Double>> inverseMatrix(ArrayList<ArrayList<Number>> matrix)
    {
        var size = matrix.size();
        var arr = new Double[size][size];
        var det = determinant(matrix);
        for (var i = 0; i <= size - 1; i++)
            for (var j = 0; j <= size - 1; j++)
            {
                var minorMt = minorMatrix(matrix, i, j);
                arr[i][j] = (determinant(minorMt) * ((i + j) % 2 == 0 ? 1 : -1)) / det;
            }
        return (ArrayList<ArrayList<Double>>) (Object) transpose((ArrayList<ArrayList<Number>>) Utilities.toArrayList(arr));
    }

    public static ArrayList<ArrayList<Number>> transpose(ArrayList<ArrayList<Number>> matrix)
    {
        var n = matrix.get(0).size();
        var res = new ArrayList<ArrayList<Number>>();
        var intContainer = new AtomicReference<Integer>();
        for (var i = 0; i <= n - 1; i++)
        {
            intContainer.set(i);
            var resRow = Utilities.map(
                    (ArrayList<Number> row) -> row.get(intContainer.get()),
                    matrix);
            res.add(resRow);
        }
        return res;
    }

    public static ArrayList<ArrayList<Number>> minorMatrix(ArrayList<ArrayList<Number>> matrix, int i, int j)
    {
        var copiedMatrix = new ArrayList<ArrayList<Number>>();
        Utilities.map(row ->
        {
            copiedMatrix.add((ArrayList<Number>) row.clone());
        }, matrix);
        copiedMatrix.remove(i);
        Utilities.map(
                row ->
                {
                    row.remove(j);
                }
                , copiedMatrix);
        return copiedMatrix;
    }

    public static double determinant(ArrayList<ArrayList<Number>> matrix)
    {
        var copiedMatrix = new ArrayList<ArrayList<Number>>();
        for (var row : matrix)
            copiedMatrix.add((ArrayList<Number>) row.clone());
        var outs = new HashMap<String, Object>();
        makeDiagonalMatrix(copiedMatrix, outs);
        var res = 1d;
        for (var i = 0; i <= copiedMatrix.size() - 1; i++)
            res *= copiedMatrix.get(i).get(i).doubleValue();
        return res * ((int) outs.get("permutationSign"));
    }

    public static void makeDiagonalMatrix(ArrayList<ArrayList<Number>> matrix,
                                          HashMap<String, Object> outs)
    {
        if (matrix.size() <= 1)
        {
            outs.put("permutationSign", 1);
            return;
        }
        var pairs0 = Utilities.table(
                i ->
                {
                    var aux = new ArrayList<>();
                    aux.add(matrix.get(i));
                    aux.add(i);
                    return aux;
                }, 0, matrix.size() - 1
        );
        var processedRowIndices = new HashSet<Integer>();
        var m = matrix.size();
        var n = matrix.get(0).size();
        var processingColumnIndex = n - 1;
        while (processedRowIndices.size() < m && processingColumnIndex >= 0)
        {
            var copiedProcessingColumnIndex = processingColumnIndex;
            var processingRowIndex = Utilities.firstCase(
                    Utilities.range(0, m - 1),
                    i ->
                    {
                        if (processedRowIndices.contains(i))
                            return false;
                        var iRow = matrix.get(i);
                        return iRow.get(copiedProcessingColumnIndex).doubleValue() != 0d;
                    }, (Integer) null);
            if (processingRowIndex == null)
            {
                processingColumnIndex--;
                continue;
            }
            var processingRow = matrix.get(processingRowIndex);
            if (NullFunction.createInstance(() ->
            {
                return Utilities.allTrue(Utilities.range(0, m - 1),
                        (Integer i) ->
                        {
                            if (i.equals(processingRowIndex))
                                return true;
                            if (processedRowIndices.contains(i))
                                return true;
                            var iRow = matrix.get(i);
                            return iRow.get(copiedProcessingColumnIndex).doubleValue() == 0d;
                        }
                );
            }).apply())
            {
                processedRowIndices.add(processingRowIndex);
                processingColumnIndex--;
                continue;
            }
            var processedRowColumnValue = processingRow.get(processingColumnIndex);
            for (var i = 0; i <= m - 1; i++)
            {
                if (processingRowIndex.equals(i))
                    continue;
                if (processedRowIndices.contains(i))
                    continue;
                var iRow = matrix.get(i);
                var iRowColumnValue = iRow.get(processingColumnIndex);
                var ratio = iRowColumnValue.doubleValue() / processedRowColumnValue.doubleValue();
                Utilities.map(
                        j ->
                        {
                            if (j.equals(copiedProcessingColumnIndex))
                                iRow.set(copiedProcessingColumnIndex, 0d);
                            else iRow.set(
                                    j, iRow.get(j).doubleValue() - ratio * processingRow.get(j).doubleValue()
                            );
                        }, Utilities.range(0, processingRow.size() - 1));
            }
        }
        Utilities.quickSort(matrix,
                (row0, row1) ->
                {
                    var auxRow0 = Utilities.map((Number x) -> Math.abs(x.doubleValue()), row0);
                    var auxRow1 = Utilities.map((Number x) -> Math.abs(x.doubleValue()), row1);
                    return Utilities.lexicographicOrder(
                            (ArrayList<Double>)(Object)Utilities.reverse(auxRow0),
                            (ArrayList<Double>)(Object) Utilities.reverse(auxRow1),
                            (x, y) -> x - y
                    );
                }
        );
        var pairs1 = Utilities.table(
                i ->
                {
                    var aux = new ArrayList<>();
                    aux.add(matrix.get(i));
                    aux.add(i);
                    return aux;
                }, 0, matrix.size() - 1
        );
        var g = new Graph<Integer>();
        for (var pair0 : pairs0)
        {
            var pair1 = Utilities.firstCase(pairs1,
                    x -> x.get(0) == pair0.get(0)
            );
            var a = (int) pair0.get(1);
            var b = (int) pair1.get(1);
            if (a != b)
                g.addEdge(a, b);
        }
        var compos = g.weaklyConnectedComponents();
        var values = Utilities.map(
                x -> x.size() % 2 == 0 ? -1 : 1
                , compos);
        var permSign = new AtomicReference<Integer>();
        permSign.set(1);
        Utilities.map(x ->
        {
            permSign.set(permSign.get() * x);
        }, values);
        outs.put("permutationSign", permSign.get());
        outs.put("independentRows", processedRowIndices);
    }
}
