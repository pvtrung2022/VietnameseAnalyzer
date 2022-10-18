package com.trung;

import java.awt.event.ActionEvent;
import java.lang.reflect.Method;
import java.util.*;
import java.util.regex.Pattern;

import com.wolfram.jlink.*;
import com.wolfram.jlink.LoopbackLink;

import java.text.Normalizer;

public class Utilities
{
    /**
     * @param col
     * @param crit
     * @param <T>
     * @return trả lại một collection với đoạn đầu và đoạn cuối của col được trim bởi hàm tiểu chuẩn crit
     */
    public static <T> Collection<T> trim(Collection<T> col, UnaryFunction<T, Boolean> crit)
    {
        var res = Utilities.trimStart(col, crit);
        return Utilities.trimEnd(res, crit);
    }

    /**
     * @param col
     * @param crit
     * @param <T>
     * @return trả lại một collection với đoạn cuối của col được trim bởi hàm tiểu chuẩn crit
     */
    public static <T> Collection<T> trimEnd(Collection<T> col, UnaryFunction<T, Boolean> crit)
    {
        var res = trimStart(Utilities.reverse(col), crit);
        return Utilities.reverse(res);
    }

    /**
     * @param col
     * @param crit
     * @param <T>
     * @return trả lại một collection với đoạn đầu của col được trim bởi hàm tiểu chuẩn crit
     */
    public static <T> Collection<T> trimStart(Collection<T> col, UnaryFunction<T, Boolean> crit)
    {
        try
        {
            var cloneMethod = getCloneMethod(col);
            var res = cloneMethod == null ? new ArrayList<T>() :
                    (Collection<T>) cloneMethod.invoke(col);
            res.clear();
            var metQ = false;
            for (var ele : col)
            {
                if (!metQ)
                    if (!crit.apply(ele))
                        metQ = true;
                if (metQ)
                    res.add(ele);
            }
            return res;
        } catch (Exception e)
        {
            throw new RuntimeException(e.getMessage());
        }
    }

    /**
     * @param obj
     * @return trả lại clone method nếu nó public trong obj
     */
    private static Method getCloneMethod(Object obj)
    {
        var methods = obj.getClass().getMethods();
        for (var method : methods)
            if (method.getName().equals("clone") && method.getParameterCount() == 0)
                return method;
        return null;
    }

    /**
     * @param ar
     * @param rules
     * @param <T>
     * @return trả lại một ArrayList sau khi thực hiện các quy tắc biến đổi của rules
     */
    public static <T> ArrayList<T> rewrite(T[] ar, HashMap<List<T>, List<T>> rules)
    {
        return rewrite(ar,
                x -> rules.containsKey(x),
                x -> rules.get(x)
        );
    }

    /**
     * @param col
     * @param rules các quy tắc cho biến đổi
     * @param <T>
     * @return trả lại một ArrayList sau khi thực hiện các quy tắc biến đổi của rules
     */
    public static <T> ArrayList<T> rewrite(Collection<T> col, HashMap<List<T>, List<T>> rules)
    {
        return rewrite(col,
                x -> rules.containsKey(x),
                x -> rules.get(x)
        );
    }

    /**
     * @param ar
     * @param checkf kiểm tra liệu dãy con có thỏa mãn điều kiện để viết lại
     * @param writef
     * @param <T>
     * @return trả lại một ArrayList sau khi thực hiện các quy tắc biến đổi của writef
     */
    public static <T> ArrayList<T> rewrite(T[] ar,
                                           UnaryFunction<List<T>, Boolean> checkf,
                                           UnaryFunction<List<T>, List<T>> writef)
    {
        var col = new ArrayList<T>();
        Utilities.map(
                x ->
                {
                    col.add(x);
                }
                , ar);
        return rewrite(col, checkf, writef);
    }

    /**
     * @param col
     * @param checkf kiểm tra liệu dãy con có thỏa mãn điều kiện để viết lại
     * @param writef
     * @param <T>
     * @return trả lại một ArrayList sau khi thực hiện các quy tắc biến đổi của writef
     */
    public static <T> ArrayList<T> rewrite(Collection<T> col,
                                           UnaryFunction<List<T>, Boolean> checkf,
                                           UnaryFunction<List<T>, List<T>> writef)
    {
        var list = new ArrayList<T>();
        list.addAll(col);
        return preRewrite(list, checkf, writef);
    }

    private static <T> ArrayList<T> preRewrite(List<T> list,
                                               UnaryFunction<List<T>, Boolean> checkf,
                                               UnaryFunction<List<T>, List<T>> writef)
    {
        var res = new ArrayList<T>();
        res.addAll(list);
        while (true)
        {
            var metQ = false;
            found:
            for (var i = 0; i <= res.size() - 1; i++)
                for (var j = i; j <= res.size() - 1; j++)
                {
                    var subIJ = Utilities.part(res, i, j);
                    if (checkf.apply(subIJ))
                    {
                        var startingPart = Utilities.part(res, 0, i - 1);
                        var endingPart = Utilities.part(res, j + 1, res.size() - 1);
                        res = Utilities.join(startingPart, writef.apply(subIJ), endingPart);
                        metQ = true;
                        break found;
                    }
                }
            if (!metQ)
                break;
        }
        return res;
    }

    /**
     * @param arr0
     * @param arr1
     * @param <T>
     * @return trả lại true nếu mảng arr0 là con của mảng arr1
     */
    public static <T> boolean isSubarray(T[] arr0, T[] arr1)
    {
        if (arr0.length > arr1.length)
            return false;
        for (var i = 0; i <= arr0.length - 1; i++)
        {
            var ele0 = arr0[i];
            var ele1 = arr1[i];
            if (!ele0.equals(ele1))
                return false;
        }
        return true;
    }

    /**
     * @param col0
     * @param col1
     * @param <T>
     * @return trả lại true nếu col0 là một subcollection của col1 tương thích với iterator, false
     * nếu khác đi
     */
    public static <T> boolean isSubcollection(Collection<T> col0, Collection<T> col1)
    {
        if (col0.size() > col1.size())
            return false;
        var it0 = col0.iterator();
        var it1 = col1.iterator();
        while (it0.hasNext())
        {
            var ele0 = it0.next();
            var ele1 = it1.next();
            if (!ele0.equals(ele1))
                return false;
        }
        return true;
    }

    /**
     * @param ar
     * @param checkf
     * @param <T>
     * @return trả lại danh sách bằng cách chạy duyệt các phần tử trong ar và bỏ qua những phần tử nào mà
     * nếu khi thêm nó vào kết quả thì không thỏa mãn hàm checkf
     */
    public static <T> ArrayList<T> selectCheck(T[] ar, UnaryFunction<ArrayList<T>, Boolean> checkf)
    {
        var col = new ArrayList<T>();
        for (var ele : ar)
            col.add(ele);
        return selectCheck(col, checkf);
    }

    /**
     * @param col
     * @param checkf
     * @param <T>
     * @return trả lại danh sách bằng cách chạy duyệt các phần tử trong col và bỏ qua những phần tử nào mà
     * nếu khi thêm nó vào kết quả thì không thỏa mãn hàm checkf
     */
    public static <T> ArrayList<T> selectCheck(Collection<T> col, UnaryFunction<ArrayList<T>, Boolean> checkf)
    {
        var res = new ArrayList<T>();
        for (var ele : col)
        {
            var auxRes = Utilities.append(res, ele);
            if (checkf.apply(auxRes))
                res.add(ele);
        }
        return res;
    }

    /**
     * xóa bỏ các keys trong hm thỏa mãn điều kiện check
     *
     * @param hm
     * @param check
     * @param <S>
     * @param <T>
     */
    public static <S, T> void removeKeys(HashMap<S, T> hm, UnaryFunction<S, Boolean> check)
    {
        var removedKeys = new HashSet<S>();
        for (var key : hm.keySet())
            if (check.apply(key))
                removedKeys.add(key);
        for (var key : removedKeys)
            hm.remove(key);
    }

    /**
     * chèn các gía trị của insertMap vào targetMap
     *
     * @param targetMap
     * @param insertMap
     * @param defaultValue giá trị để thiết lập giá trị mặc định cho các keys trong insertMap nếu nó vẫn chưa có sẵn trong targetMap
     * @param func         hàm này đi từ giá trị hiện tại của targetMap và giá trị hiện tại của insertMap để thiết lập giá trị mới cho targetMap
     * @param <S>
     * @param <T>
     * @param <U>
     * @param <R>
     * @param <W>
     */
    public static <S, T, U, R, W> void insertValues(HashMap<S, T> targetMap,
                                                    HashMap insertMap,
                                                    NullFunction<R> defaultValue,
                                                    BinaryFunction<R, W, R> func)
    {
        insertValues(targetMap, insertMap, new ArrayList<>(), defaultValue, func);
    }

    private static <S, T, U, V, R, W> void insertValues(HashMap<S, T> targetMap,
                                                        U insertObj,
                                                        List<V> prefix,
                                                        NullFunction<R> defaultValue,
                                                        BinaryFunction<R, W, R> func)
    {
        if (!(insertObj instanceof HashMap))
        {
            var prefixArr = prefix.toArray();
            Utilities.insertValue(targetMap, prefixArr,
                    defaultValue.apply(),
                    x -> func.apply(x, (W) insertObj)
            );
        } else
        {
            var insertObjOrigin = (HashMap) insertObj;
            for (var key : insertObjOrigin.keySet())
            {
                var value = insertObjOrigin.get(key);
                var newPrefix = new ArrayList<V>();
                newPrefix.addAll(prefix);
                newPrefix.add((V) key);
                insertValues(targetMap,
                        value,
                        newPrefix, defaultValue, func
                );
            }
        }
    }

    /**
     * @param obj
     * @param map
     * @param level
     * @return trả lại một Object với các phần tử trong obj được thay thế bởi map tại level
     */
    public static Object replace(Object obj, Map map, int level)
    {
        if (level < 0)
            throw new RuntimeException("invalid level");
        if (level == 0)
        {
            if (map.containsKey(obj))
                return map.get(obj);
            else return obj;
        }
        var cloneMethod = getCloneMethod(obj);
        if (obj instanceof Collection)
        {
            var originObj = (Collection) obj;
            Collection res = (obj instanceof Set) ? new HashSet<>() : new ArrayList<>();
            if (cloneMethod != null)
                try
                {
                    res = (Collection) cloneMethod.invoke(obj);
                    res.clear();
                } catch (Exception e)
                {
                }
            for (var ele : originObj)
                res.add(replace(ele, map, level - 1));
            return res;
        }
        if (obj instanceof Map)
        {
            var originObj = (Map) obj;
            Map res = new HashMap<>();
            if (cloneMethod != null)
                try
                {
                    res = (Map) cloneMethod.invoke(obj);
                    res.clear();
                } catch (Exception e)
                {
                }
            for (var key : originObj.keySet())
            {
                var value = originObj.get(key);
                res.put(
                        replace(key, map, level - 1),
                        replace(value, map, level - 1)
                );
            }
            return res;
        }
        return obj;
    }

    public static Object replaceAll(Object obj, Map map)
    {
        if (map.containsKey(obj))
            return map.get(obj);
        var cloneMethod = getCloneMethod(obj);
        if (obj instanceof Collection)
        {
            var objOrigin = (Collection) obj;
            Collection res;
            if (obj instanceof Set)
                res = new HashSet<>();
            else res = new ArrayList<>();
            if (cloneMethod != null)
            {
                try
                {
                    res = (Collection) cloneMethod.invoke(obj);
                    res.clear();
                } catch (Exception e)
                {
                }
            }
            for (var ele : objOrigin)
                res.add(replaceAll(ele, map));
            return res;
        }
        if (obj instanceof Map)
        {
            var objOrigin = (Map) obj;
            Map res;
            res = new HashMap<>();
            if (cloneMethod != null)
            {
                try
                {
                    res = (Map) cloneMethod.invoke(obj);
                    res.clear();
                } catch (Exception e)
                {
                }
            }
            for (var key : objOrigin.keySet())
            {
                var value = objOrigin.get(key);
                var keyRes = replaceAll(key, map);
                var valueRes = replaceAll(value, map);
                res.put(keyRes, valueRes);
            }
            return res;
        }
        return obj;
    }

    public static <T> ArrayList<ArrayList<T>> cartesianProduct(Collection<T>... cols)
    {
        if (cols.length == 0)
            throw new RuntimeException("The input is not valid");
        else if (cols.length == 1)
        {
            var col = cols[0];
            var res = Utilities.map((x) ->
            {
                var aux = new ArrayList<T>();
                aux.add(x);
                return aux;
            }, col);
            return res;
        } else
        {
            var subInput = new Collection[cols.length - 1];
            for (var i = 0; i <= cols.length - 2; i++)
                subInput[i] = cols[i];
            var subRes = (ArrayList<ArrayList<T>>) (Object) cartesianProduct(subInput);
            var lastCol = cols[cols.length - 1];
            var res = new ArrayList<ArrayList<T>>();
            for (var tuple : subRes)
                for (var ele : lastCol)
                {
                    var copiedTuple = (ArrayList<T>) tuple.clone();
                    copiedTuple.add(ele);
                    res.add(copiedTuple);
                }
            return res;
        }
    }

    public static <T> boolean isIntersecting(Collection<T> col0, Collection<T> col1)
    {
        for (var ele : col0)
            if (col1.contains(ele))
                return true;
        return false;
    }

    public static <T> HashSet<T> intersection(Collection<T> col0, Collection<T> col1)
    {
        var res = new HashSet<T>();
        for (var ele : col0)
            if (col1.contains(ele))
                res.add(ele);
        return res;
    }

    /**
     *
     * @param col
     * @param func
     * @return kiểm tra một collection có được sắp xếp với hàm giá trị func
     * @param <T>
     */
    public static <T> boolean isOrdered(List<T> col, UnaryFunction<T, ? extends Number> func)
    {
        return isOrdered(col, (x, y) -> func.apply(x).doubleValue() - func.apply(y).doubleValue());
    }

    /**
     *
     * @param array
     * @param func
     * @return kiểm tra một mảng có được sắp xếp với hàm giá trị func
     * @param <T>
     */
    public static <T> boolean isOrdered(T[] array, UnaryFunction<T, ? extends Number> func)
    {
        return isOrdered(array, (x, y) -> func.apply(x).doubleValue() - func.apply(y).doubleValue());
    }

    /**
     *
     * @param array
     * @param comparator
     * @return kiểm tra một mảng có được sắp xếp với hàm so sánh comparator
     * @param <T>
     */
    public static <T> boolean isOrdered(T[] array, BinaryFunction<T, T, ? extends Number> comparator)
    {
        for (var i = 0; i <= array.length - 2; i++)
        {
            var iEle = array[i];
            var nextIEle = array[i + 1];
            if (comparator.apply(iEle, nextIEle).doubleValue() >= 0d)
                return false;
        }
        return true;
    }

    /**
     *
     * @param col
     * @param comparator
     * @return kiểm tra một collection có được sắp xếp với hàm so sánh comparator
     * @param <T>
     */
    public static <T> boolean isOrdered(List<T> col, BinaryFunction<T, T, ? extends Number> comparator)
    {
        var array = col.toArray();
        return isOrdered(array, (x, y) ->
        {
            var Tx = (T) x;
            var Ty = (T) y;
            return comparator.apply(Tx, Ty);
        });
    }

    public static boolean isNormalized(String s)
    {
        return Normalizer.isNormalized(s, Normalizer.Form.NFC);
    }

    public static String normalizeText(String s)
    {
        return Normalizer.normalize(s, Normalizer.Form.NFC);
    }

    /**
     * @param col
     * @param sameQ
     * @param <T>
     * @return trả lại một danh sách các phần tử trong col sao cho các phần tử lặp lại bởi hàm sameQ sẽ được
     * bỏ đi. Chú ý rằng thứ tự trong danh sách trả lại tương thích với iterator của col
     */
    public static <T> ArrayList<T> deleteDuplicates(Collection<T> col, BinaryFunction<T, T, Boolean> sameQ)
    {
        var res = new ArrayList<T>();
        for (var ele : col)
        {
            if (!Utilities.anyTrue(res, (x) -> sameQ.apply(x, ele)))
                res.add(ele);
        }
        return res;
    }

    public static <T> HashSet<HashSet<T>> gatherBy(Collection<T> col, BinaryFunction<T, T, Boolean> equalFunc)
    {
        var g = new Graph<T>(col, new HashSet<ArrayList<T>>());
        for (var ele0 : col)
            for (var ele1 : col)
            {
                if (ele0.equals(ele1))
                    continue;
                else if (equalFunc.apply(ele0, ele1))
                    g.addEdge(ele0, ele1);
            }
        return g.weaklyConnectedComponents();
    }

    public static <T> HashSet<HashSet<T>> gatherBy(Collection<T> col, UnaryFunction<T, ? extends Comparable> func)
    {
        var res = new HashMap<Object, HashSet<T>>();
        for (var ele : col)
        {
            var value = func.apply(ele);
            if (!res.containsKey(value))
                res.put(value, new HashSet<T>());
            res.get(value).add(ele);
        }
        var mainRes = new HashSet<HashSet<T>>();
        for (var key : res.keySet())
            mainRes.add(res.get(key));
        return mainRes;
    }

    public static BinaryFunction convertToBinaryFunction(Expr exprFunc)
    {
        try
        {
            var lb0 = new com.trung.LoopbackLink();
            lb0.putFunction("ToString", 2);
            lb0.put(exprFunc);
            lb0.putSymbol("InputForm");
            var toSExpr = lb0.getExpr();
            var exprStr = Utilities.evaluateExpr(toSExpr).asString();
            var evaStr = exprStr + "[%0,%1]";
            return new BinaryFunctionClass((Object x, Object y) ->
            {
                return Utilities.executeMathematicaCode(evaStr, x, y);
            });
        } catch (Exception e)
        {
            throw new RuntimeException(e.getMessage());
        }
    }

    public static UnaryFunction convertToUnaryFunction(Expr exprFunc)
    {
        try
        {
            var lb0 = new com.trung.LoopbackLink();
            lb0.putFunction("ToString", 2);
            lb0.put(exprFunc);
            lb0.putSymbol("InputForm");
            var toSExpr = lb0.getExpr();
            var exprStr = Utilities.evaluateExpr(toSExpr).asString();
            var evaStr = exprStr + "[%0]";
            return new UnaryFunctionClass((Object x) ->
            {
                return Utilities.executeMathematicaCode(evaStr, x);
            });
        } catch (Exception e)
        {
            throw new RuntimeException(e.getMessage());
        }
    }

    /**
     * xóa các phần tử e trong col thỏa mãn crit
     *
     * @param col
     * @param crit
     * @param <T>
     */
    public static <T> void deleteCases(Collection<T> col, UnaryFunction<T, Boolean> crit)
    {
        var removedEles = Utilities.select(col, crit);
        col.removeAll(removedEles);
    }

    /**
     * @param col0
     * @param col1
     * @param <T>
     * @return true nếu col0 chứa tất cả các phần tử của col1, false nếu khác đi
     */
    public static <T> boolean containsAll(Collection<T> col0, Collection<T> col1)
    {
        for (var ele : col1)
            if (!col0.contains(ele))
                return false;
        return true;
    }

    /**
     * @param arr
     * @return trả lại một Object trong đó cố gắng biến đổi Collection or Array thành một ArrayList nếu có thể
     */
    public static Object toArrayList(Object arr)
    {
        var res = new ArrayList<>();
        var typeName = arr.getClass().getTypeName();
        if (arr instanceof Collection)
        {
            var origin = (Collection) arr;
            for (var obj : origin)
                res.add(toArrayList(obj));
            return res;
        } else if (typeName.contains("["))
        {
            var arObj = (Object[]) arr;
            for (var obj : arObj)
                res.add(toArrayList(obj));
            return res;
        } else return arr;
    }

    public static <T> ArrayList<ArrayList<T>> splitBy(List<T> list, UnaryFunction<T, Boolean> splitFunc)
    {
        var res = new ArrayList<ArrayList<T>>();
        var runningGroup = new ArrayList<T>();
        for (var i = 0; i <= list.size() - 1; i++)
        {
            var iEle = list.get(i);
            if (splitFunc.apply(iEle))
            {
                res.add(runningGroup);
                runningGroup = new ArrayList<>();
            } else
            {
                runningGroup.add(iEle);
            }
        }
        res.add(runningGroup);
        return res;
    }

    public static <T> int lexicographicOrder(List<T> list0, List<T> list1, BinaryFunction<T, T, ? extends Number> comparator)
    {
        var maxLength = Math.max(list0.size(), list1.size());
        for (var i = 0; i <= maxLength - 1; i++)
        {
            if (i > list0.size() - 1)
                return -1;
            if (i > list1.size() - 1)
                return 1;
            var value = comparator.apply(list0.get(i), list1.get(i)).doubleValue();
            if (value != 0)
                return value < 0 ? -1 : 1;
        }
        return 0;
    }

    public static <T> boolean memberQ(T[] eles, T ele)
    {
        return memberQ(eles, x -> x.equals(ele));
    }

    /**
     * @param eles
     * @param crit
     * @param <T>
     * @return trả lại True nếu eles có chứa một phần tử e sao cho crit.apply(e) là True, False nếu khác đi
     */
    public static <T> boolean memberQ(T[] eles, UnaryFunction<T, Boolean> crit)
    {
        for (var ele : eles)
            if (crit.apply(ele))
                return true;
        return false;
    }

    /**
     * @param eles
     * @param crit
     * @param <T>
     * @return trả lại True nếu eles có chứa một phần tử e sao cho crit.apply(e) là True, False nếu khác đi
     */
    public static <T> boolean memberQ(Collection<T> eles, UnaryFunction<T, Boolean> crit)
    {
        return anyTrue(eles, crit);
    }

    public static Container Container = new Container();

    /**
     * @param regex
     * @param s
     * @return trả lại true nếu s matches regular epxression regex, false nếu khác đi
     */
    public static boolean isMatchQ(String regex, String s)
    {
        var pattern = Pattern.compile(regex);
        var matcher = pattern.matcher(s);
        return matcher.find();
    }

    /**
     * @param list
     * @param crit
     * @param <T>
     * @return trả lại ví trí cuối cùng của phần tử trong col thỏa mãn crit
     */
    public static <T> Integer lastPosition(List<T> list, UnaryFunction<T, Boolean> crit)
    {
        var size = list.size();
        for (var i = size - 1; i >= 0; i--)
        {
            if (crit.apply(list.get(i)))
                return i;
        }
        return null;
    }

    /**
     * @param col
     * @param crit
     * @param <T>
     * @return trả lại vị trí của phần tử đầu tiên trong col thỏa mãn crit
     */
    public static <T> Integer firstPosition(Collection<T> col, UnaryFunction<T, Boolean> crit)
    {
        var it = col.iterator();
        var pos = -1;
        while (it.hasNext())
        {
            pos++;
            var ele = it.next();
            if (crit.apply(ele))
                return pos;
        }
        return null;
    }

    /**
     * @param col
     * @param crit
     * @param <T>
     * @return trả lại danh sách các vị trí của các phần tử ele trong col thỏa mãn crit.apply(ele)
     */
    public static <T> ArrayList<Integer> positions(Collection<T> col, UnaryFunction<T, Boolean> crit)
    {
        var res = new ArrayList<Integer>();
        var it = col.iterator();
        var pos = -1;
        while (it.hasNext())
        {
            pos++;
            var ele = it.next();
            if (crit.apply(ele))
                res.add(pos);
        }
        return res;
    }

    /**
     * @param list
     * @param m
     * @param n
     * @param <T>
     * @return trả lại một ArrayList với các phần tử trong list từ vị trí m đến vị trí n
     */
    public static <T> ArrayList<T> part(List<T> list, int m, int n)
    {
        var res = new ArrayList<T>();
        for (var i = m; i <= n; i++)
            res.add(list.get(i));
        return res;
    }

    /**
     * @param obj đối tượng này được hình thành bởi sự kết hợp của Collection,Map,String,long,double,integer
     * @return trả lại Expr tương ứng với Collection được chuyển thành List,Map được chuyển thành Association,
     * và các giá trị cơ bản được chuyển thành tương ứng. Nếu obj là một ExprConvertible thì được chuyển bởi hàm toExpr tương ứng
     */
    public static Expr convertToExpr(Object obj)
    {
        var loopbackLink = new com.trung.LoopbackLink();
        if (obj instanceof Number)
        {
            if (obj instanceof Long)
            {
                var origin = (long) obj;
                loopbackLink.put(origin);
                return loopbackLink.getExpr();
            }
            if (obj instanceof Integer)
            {
                var origin = (Integer) obj;
                loopbackLink.put(origin);
                return loopbackLink.getExpr();
            }
            if (obj instanceof Double)
            {
                var origin = (Double) obj;
                loopbackLink.put(origin);
                return loopbackLink.getExpr();
            }
        }
        if (obj instanceof String)
        {
            loopbackLink.put((String) obj);
            return loopbackLink.getExpr();
        }
        if (obj instanceof Collection)
        {
            var origin = (Collection) obj;
            loopbackLink.putFunction("List", origin.size());
            for (var ele : origin)
            {
                var eleExpr = convertToExpr(ele);
                loopbackLink.put(eleExpr);
            }
            return loopbackLink.getExpr();
        }
        if (obj instanceof Map)
        {
            var origin = (Map) obj;
            loopbackLink.putFunction("Association", origin.size());
            for (var key : origin.keySet())
            {
                var value = origin.get(key);
                var keyExpr = convertToExpr(key);
                var valueExpr = convertToExpr(value);
                loopbackLink.putFunction("Rule", 2);
                loopbackLink.put(keyExpr);
                loopbackLink.put(valueExpr);
            }
            return loopbackLink.getExpr();
        }
        if (obj instanceof ExprConvertible)
        {
            var origin = (ExprConvertible) obj;
            return origin.toExpr();
        }
        throw new RuntimeException("The input: " + obj.toString() + " is not valid");
    }

    public static int LCM(Collection<Integer> ints)
    {
        Integer res = null;
        for (var ele : ints)
        {
            if (res == null)
                res = ele;
            else res = LCM(res.intValue(), ele.intValue());
        }
        return res.intValue();
    }

    public static int LCM(int a, int b)
    {
        int wa = a < 0 ? -a : a;
        int wb = b < 0 ? -b : b;
        if (wa == 0 || wb == 0)
            return 0;
        return (wa * wb) / GCD(wa, wb);
    }

    public static int GCD(Collection<Integer> ints)
    {
        Integer res = null;
        for (var ele : ints)
        {
            if (res == null)
                res = ele;
            else res = GCD(res.intValue(), ele.intValue());
        }
        return res.intValue();
    }

    public static int GCD(int a, int b)
    {
        var wa = a < 0 ? -a : a;
        var wb = b < 0 ? -b : b;
        if (wa == 0 && wb == 0)
            throw new RuntimeException("invalid input");
        while (true)
        {
            if (wa == 0)
                return wb;
            if (wb == 0)
                return wa;
            if (wa >= wb)
            {
                int x = wa / wb;
                wa = wa - x * wb;
            } else
            {
                int x = wb / wa;
                wb = wb - x * wa;
            }
        }
    }

    public static <S, T, U> Object getValue(HashMap<S, T> hm, U... keys)
    {
        Object res = hm;
        for (var key : keys)
        {
            if (!(res instanceof HashMap))
                return null;
            var origin = (HashMap<Object, Object>) res;
            if (!origin.containsKey(key))
                return null;
            res = origin.get(key);
        }
        return res;
    }

    /**
     * @param hm
     * @param keys
     * @param defaultValue giá trị này mang nghĩa là nếu hm không chứa keys thì sẽ chèn giá trị mặc định này vào hm với keys
     * @param newValueFunc đây là hàm đi từ giá trị hiện tại của keys tới giá trị mới của keys
     * @param <S>
     * @param <T>
     * @param <U>
     * @param <V>
     * @param <R>
     */
    public static <S, T, U, V, R> void insertValue(HashMap<S, T> hm, U[] keys, V defaultValue, UnaryFunction<V, R> newValueFunc)
    {
        if (!Utilities.keySequenceExistsQ(hm, keys))
            Utilities.insertValue(hm, keys, defaultValue);
        var currentValue = (V) Utilities.getValue(hm, keys);
        Utilities.insertValue(hm, keys, newValueFunc.apply(currentValue));
    }

    public static <S, T, U, V> void insertValue(HashMap<S, T> hm, U[] keys, V value)
    {
        Object running = hm;
        for (var i = 0; i <= keys.length - 2; i++)
        {
            var key = keys[i];
            if (!(hm instanceof HashMap))
                return;
            var origin = (HashMap<Object, Object>) running;
            if (!origin.containsKey(key))
                origin.put(key, new HashMap<>());
            running = origin.get(key);
        }
        if (!(running instanceof HashMap))
            return;
        var origin = (HashMap<Object, Object>) running;
        var lastKey = keys[keys.length - 1];
        origin.put(lastKey, value);
    }


    public static <S, T, U> boolean keySequenceExistsQ(HashMap<S, T> hm, U... keys)
    {
        Object running = hm;
        for (var i = 0; i <= keys.length - 1; i++)
        {
            var key = keys[i];
            if (!(running instanceof HashMap))
                return false;
            var origin = (HashMap) running;
            if (!origin.containsKey(key))
                return false;
            running = origin.get(key);
        }
        return true;
    }

    /**
     * biến này dùng để chuyển giá trị giữa Mathematica và Java
     */
    public static Object transferredValue = null;

    public static <T> T getArrayElement(T[] ar, int pos)
    {
        return ar[pos];
    }

    /**
     * @param s
     * @param rules
     * @return thay thế chuỗi con trong chuỗi s một cách đồng thời theo các quy tắc trong rules
     */
    public static String stringReplace(String s, HashMap<String, String> rules)
    {
        var res = "";
        var runningIndex = 0;
        while (runningIndex <= s.length() - 1)
        {
            var subS = s.substring(runningIndex);
            var meetQ = false;
            for (var key : rules.keySet())
            {
                if (subS.startsWith(key))
                {
                    res += rules.get(key);
                    runningIndex += key.length();
                    meetQ = true;
                    break;
                }
            }
            if (!meetQ)
            {
                res += s.charAt(runningIndex);
                runningIndex++;
            }
        }
        return res;
    }

    private static <T> Collection<T> makeAnEmptyClone(Collection<T> col)
    {
        var cloneMethod = getCloneMethod(col);
        return cloneMethod == null ? NullFunction.createInstance(() ->
        {
            Collection<T> aux = null;
            if (col instanceof Set)
                aux = new HashSet<>();
            else aux = new ArrayList<>();
            return aux;
        }).apply() : NullFunction.createInstance(() ->
        {
            try
            {
                var aux = (Collection<T>) cloneMethod.invoke(col);
                aux.clear();
                return aux;
            } catch (Exception e)
            {
                throw new RuntimeException(e.getMessage());
            }
        }).apply();
    }

    /**
     * @param col
     * @param <T>
     * @return trả lại một danh sách các phần tử của eles trong thứ tự đảo ngược
     */
    public static <T> Collection<T> reverse(Collection<T> col)
    {
        var res = makeAnEmptyClone(col);
        if (col instanceof List)
        {
            var originCol = (List<T>) col;
            var size = originCol.size();
            for (var i = size - 1; i >= 0; i--)
                res.add(originCol.get(i));
            return res;
        } else
        {
            var arraylistRes = new ArrayList<T>();
            for (var ele : col)
                arraylistRes.add(0, ele);
            for (var ele : arraylistRes)
                res.add(ele);
            return res;
        }
    }

    public static <T extends Number> ArrayList<ArrayList<Double>> inverseMatrix(ArrayList<ArrayList<T>> matrix)
    {
        var code = arrayListToMcode(matrix);
        var mainCode = "Inverse[code]//N";
        mainCode = mainCode.replace("code", code);
        var auxRes = (Expr) Utilities.executeMathematicaCode(mainCode);
        var res = new ArrayList<ArrayList<Double>>();
        for (var row : auxRes.args())
        {
            var resRow = new ArrayList<Double>();
            for (var ele : row.args())
            {
                var value = Double.parseDouble(ele.toString());
                resRow.add(value);
            }
            res.add(resRow);
        }
        return res;
    }

    private static String arrayListToMcode(ArrayList ele)
    {
        var res = ele.toString();
        res = res.replace("[", "{");
        res = res.replace("]", "}");
        return res;
    }

    public static int LevenshteinDistance(List a, List b)
    {
        if (a.size() == 0)
            return b.size();
        if (b.size() == 0)
            return a.size();
        var firsta = a.get(0);
        var firstb = b.get(0);
        var taila = Utilities.map((Integer pos) -> a.get(pos), Utilities.range(1, a.size() - 1));
        var tailb = Utilities.map((Integer pos) -> b.get(pos), Utilities.range(1, b.size() - 1));
        if (firsta.equals(firstb))
            return LevenshteinDistance(taila, tailb);
        var aux0 = LevenshteinDistance(taila, b);
        var aux1 = LevenshteinDistance(a, tailb);
        var aux2 = LevenshteinDistance(taila, tailb);
        return 1 + Utilities.min(aux0, aux1, aux2);
    }

    public static <T> T randomChoice(Collection<T> eles)
    {
        var size = eles.size();
        if (size == 0)
            throw new RuntimeException("empty collection");
        var rand = new Random();
        var randIndex = rand.nextInt(size);
        if (eles instanceof List)
        {
            var list = (List<T>) eles;
            return list.get(randIndex);
        } else
        {
            var it = eles.iterator();
            var count = 0;
            T res = null;
            while (count != randIndex + 1)
            {
                res = it.next();
                count++;
            }
            return res;
        }
    }

    public static <T> void topologicalSort(ArrayList<T> eles, BinaryFunction<T, T, ? extends Number> comparator)
    {
        var g = new Graph<Integer>();
        for (var i = 0; i <= eles.size() - 1; i++)
            g.addVertex(i);
        for (var i = 0; i <= eles.size() - 2; i++)
        {
            var iEle = eles.get(i);
            for (var j = i + 1; j <= eles.size() - 1; j++)
            {
                var jEle = eles.get(j);
                var com = comparator.apply(iEle, jEle).doubleValue();
                if (com != 0)
                {
                    if (com < 0)
                        g.addEdge(i, j);
                    else g.addEdge(j, i);
                }
            }
        }
        var intsSorted = topologicalSort(g);
        var sortedEles = new ArrayList<T>();
        for (var index : intsSorted)
            sortedEles.add(eles.get(index));
        eles.clear();
        eles.addAll(sortedEles);
    }

    public static <T> ArrayList<T> topologicalSort(Graph<T> g)
    {
        var wg = (Graph<T>) g.clone();
        var res = new ArrayList<T>();
        while (wg.vertexCount() > 0)
        {

            var degrees = Utilities.map((T v) -> wg.vertexInDegree(v),
                    wg.vertexList());
            var minDegree = Utilities.min(degrees, (x, y) -> x - y);

            var selectedVs = Utilities.select(wg.vertexList(),
                    (v) -> wg.vertexInDegree(v) == minDegree
            );
            if (selectedVs.size() == 0)
                return res;
            else
            {
                res.addAll(selectedVs);
                wg.deleteVertices(selectedVs);
            }
        }
        return res;
    }

    /**
     * @param f
     * @param col
     * @param <S>
     * @return trả lại tổng khi f chạy trên các phần tử trong col
     */
    public static <S> double sum(UnaryFunction<S, ? extends Number> f, S[] col)
    {
        var res = 0d;
        for (var ele : col)
            res += (f.apply(ele).doubleValue());
        return res;
    }

    /**
     * @param f
     * @param col
     * @param <S>
     * @return trả lại tổng khi f chạy trên các phần tử trong col
     */
    public static <S> double sum(UnaryFunction<S, ? extends Number> f, Collection<S> col)
    {
        var res = 0d;
        for (var ele : col)
            res += (f.apply(ele).doubleValue());
        return res;
    }

    /**
     * @param values
     * @return trả lại tổng các phần tử trong values
     */
    public static double sum(Collection<? extends Number> values)
    {
        var res = 0d;
        for (var value : values)
            res += value.doubleValue();
        return res;
    }

    /**
     * @param values
     * @return trả lại tích các phần tử trong values
     */
    public static double product(Collection<? extends Number> values)
    {
        var res = 1d;
        for (var value : values)
            res *= value.doubleValue();
        return res;
    }

    /**
     * @param f
     * @param col
     * @param <S>
     * @return trả lại tích khi f chạy trên các phần tử trong col
     */
    public static <S> double product(UnaryFunction<S, ? extends Number> f, Collection<S> col)
    {
        var res = 1d;
        for (var ele : col)
            res *= (f.apply(ele).doubleValue());
        return res;
    }

    /**
     * @param values
     * @return trả lại variance của các giá trị values
     */

    public static double variance(Collection<? extends Number> values)
    {
        var m = mean(values);
        var res = 0d;
        var count = 0;
        for (var value : values)
        {
            var dvalue = value.doubleValue();
            res += ((dvalue - m) * (dvalue - m));
            count++;
        }
        return Math.sqrt(res / count);
    }

    /**
     * @param values
     * @return giá trị trung bình của các giá trị values
     */
    public static double mean(Collection<? extends Number> values)
    {
        var res = 0d;
        var count = 0;
        for (var value : values)
        {
            res += value.doubleValue();
            count++;
        }
        return res / count;
    }


    /**
     * @param eles
     * @param <T>
     * @return trả lại một danh sách các phần tử có trong eles
     */
    public static <T> ArrayList<T> makeArrayList(Collection<T> eles)
    {
        var res = new ArrayList<T>();
        for (var ele : eles)
            res.add(ele);
        return res;
    }

    /**
     * @param eles
     * @param <T>
     * @return trả lại một HashSet bao gồm các phần tử trong eles
     */
    public static <T> HashSet<T> makeHashSet(Collection<T> eles)
    {
        var res = new HashSet<T>();
        for (var ele : eles)
            res.add(ele);
        return res;
    }

    /**
     * @param eles
     * @param check
     * @param after
     * @param <S>
     * @param <T>
     * @return trả lại phần tử được after áp dụng lên phần tử đầu tiên được tìm thấy trong eles thỏa mãn hàm kiểm tra check
     */
    public static <S, T> T firstCase(Collection<S> eles, UnaryFunction<S, Boolean> check, UnaryFunction<S, T> after)
    {
        for (var ele : eles)
            if (check.apply(ele))
                return after.apply(ele);
        throw new RuntimeException("Case missing");
    }

    /**
     * @param eles
     * @param check
     * @param missingObj
     * @param <T>
     * @return trả lại phần tử đầu tiên được tìm thấy trong eles thỏa mãn hàm kiểm tra check, nếu không tìm thấy thì trả
     * lại phần tử missingObj
     */
    public static <T> T firstCase(Collection<T> eles, UnaryFunction<T, Boolean> check, T missingObj)
    {
        try
        {
            return firstCase(eles, check);
        } catch (Exception e)
        {
            return missingObj;
        }
    }

    /**
     * @param eles
     * @param check
     * @param <T>
     * @return trả lại phần tử đầu tiên được tìm thấy trong eles thỏa mãn hàm kiểm tra check
     */
    public static <T> T firstCase(Collection<T> eles, UnaryFunction<T, Boolean> check)
    {
        for (var ele : eles)
            if (check.apply(ele))
                return ele;
        throw new RuntimeException("case missing");
    }

    /**
     * @param eles
     * @param addedEle
     * @param <T>
     * @return trả lại danh sách bằng cách thêm phần tử addedEle vào trước eles
     */
    public static <T> ArrayList<T> prepend(Collection<T> eles, T addedEle)
    {
        var res = new ArrayList<T>();
        res.add(addedEle);
        for (var ele : eles)
            res.add(ele);
        return res;
    }

    /**
     * @param eles
     * @param addedEle
     * @param <T>
     * @return trả lại danh sách bằng cách thêm phần tử addedEle vào cuối danh sách eles
     */
    public static <T> ArrayList<T> append(Collection<T> eles, T addedEle)
    {
        var res = new ArrayList<T>();
        for (var ele : eles)
            res.add(ele);
        res.add(addedEle);
        return res;
    }

    /**
     * @param eles
     * @param minIndex
     * @param maxIndex
     * @param <T>
     * @return cho ra danh sách các phần tử từ vị trí nhỏ nhất minIndex đến vị trí lớn nhất maxIndex trong eles
     */
    public static <T> ArrayList<T> part(Collection<T> eles, int minIndex, int maxIndex)
    {
        var res = new ArrayList<T>();
        if (eles instanceof List)
        {
            var origin = (List<T>) eles;
            for (var i = minIndex; i <= maxIndex; i++)
                res.add(origin.get(i));
            return res;
        } else
        {
            var it = eles.iterator();
            for (var i = 0; i <= minIndex - 1; i++)
                it.next();
            for (var i = minIndex; i <= maxIndex; i++)
                res.add(it.next());
            return res;
        }
    }

    /**
     * trả lại danh sách các phần tử khi áp dụng hàm func lên phần tử chạy từ iMin đến iMax với bước
     * nhảy 1
     *
     * @param func
     * @param iMin
     * @param iMax
     * @param <T>
     * @return
     */
    public static <T> ArrayList<T> table(UnaryFunction<Integer, T> func, int iMin, int iMax)
    {
        return table(func, iMin, iMax, 1);
    }

    /**
     * trả lại danh sách các phần tử khi áp dụng hàm func lên phần tử chạy từ iMin đến iMax với bước
     * nhảy d
     *
     * @param func
     * @param iMin
     * @param iMax
     * @param d
     * @param <T>
     * @return
     */
    public static <T> ArrayList<T> table(UnaryFunction<Integer, T> func, int iMin, int iMax, int d)
    {
        var res = new ArrayList<T>();
        for (var i = iMin; i <= iMax; i += d)
            res.add(func.apply(i));
        return res;
    }

    /**
     * @param min
     * @param max
     * @return trả lại danh sách các số tự nhiên liên tiếp từ min đến max
     */
    public static ArrayList<Integer> range(int min, int max)
    {
        var res = new ArrayList<Integer>();
        for (var i = min; i <= max; i++)
            res.add(i);
        return res;
    }

    /**
     * @param eles
     * @param n
     * @param <T>
     * @return trả lại phần tử thứ (n+1) trong eles
     */
    public static <T> T getElement(Collection<T> eles, int n)
    {
        if (eles.size() < n + 1 || n < 0)
            throw new RuntimeException("missing element");
        else if (eles instanceof List)
        {
            var origin = (List<T>) eles;
            return origin.get(n);
        } else
        {
            var count = 0;
            for (var ele : eles)
            {
                count++;
                if (count == n + 1)
                    return ele;
            }
            throw new RuntimeException("missing element");
        }
    }

    public static <T> T getLastElement(Collection<T> eles)
    {
        if (eles instanceof List)
        {
            var origin = (List<T>) eles;
            return origin.get(origin.size() - 1);
        } else
        {
            var size = eles.size();
            var it = eles.iterator();
            for (var i = 0; i <= size - 2; i++)
                it.next();
            return it.next();
        }
    }

    /**
     * @param eles
     * @param <T>
     * @return trả lại phần tử đầu tiên trong eles
     */
    public static <T> T getFirstElement(Collection<T> eles)
    {
        var it = eles.iterator();
        return it.next();
    }

    public static <T extends Number> T max(T... eles)
    {
        if (eles.length == 0)
            throw new RuntimeException("Empty input");
        var res = eles[0];
        for (var i = 1; i <= eles.length - 1; i++)
            if (eles[i].doubleValue() > res.doubleValue())
                res = eles[i];
        return res;
    }

    public static <T extends Number> T min(T... eles)
    {
        if (eles.length == 0)
            throw new RuntimeException("Empty input");
        var res = eles[0];
        for (var i = 1; i <= eles.length - 1; i++)
            if (eles[i].doubleValue() < res.doubleValue())
                res = eles[i];
        return res;
    }

    /**
     * @param eles
     * @param <T>
     * @return trả lại phần tử bé nhất trong các  phần tử eles so sánh được với nhau
     */
    public static <T extends Comparable> T min(Collection<T> eles)
    {
        return min(eles,
                (x, y) -> x.compareTo(y)
        );
    }

    public static <T> HashSet<T> maximals(Collection<T> col, BinaryFunction<T, T, ? extends Number> comparator)
    {
        return minimals(col,
                (x, y) -> -comparator.apply(x, y).doubleValue()
        );
    }

    public static <T> HashSet<T> minimals(Collection<T> col, BinaryFunction<T, T, ? extends Number> comparator)
    {
        var res = new HashSet<T>();
        var comparatorValues = new HashMap<>();
        for (var ele : col)
        {
            if (res.size() == 0)
                res.add(ele);
            else
            {
                var aboves = Utilities.select(res,
                        (x) ->
                        {
                            if (!Utilities.keySequenceExistsQ(comparatorValues, ele, x))
                                Utilities.insertValue(comparatorValues, new Object[]{ele, x}, comparator.apply(ele, x));
                            var value = ((Number) Utilities.getValue(comparatorValues, ele, x)).doubleValue();
                            return value < 0;
                        }
                );
                if (aboves.size() != 0)
                {
                    res.removeAll(aboves);
                    res.add(ele);
                    continue;
                }
                var belows = Utilities.select(res,
                        (x) ->
                        {
                            if (!Utilities.keySequenceExistsQ(comparatorValues, ele, x))
                                Utilities.insertValue(comparatorValues, new Object[]{ele, x}, comparator.apply(ele, x));
                            var value = ((Number) Utilities.getValue(comparatorValues, ele, x)).doubleValue();
                            return value > 0;
                        }
                );
                if (belows.size() == 0)
                    res.add(ele);
            }
        }
        return res;
    }

    /**
     * @param eles
     * @param comparator
     * @param <T>
     * @return trả lại phẩn tử nhỏ nhất trong eles tương ứng với hàm so sánh comparator
     */
    public static <T> T min(Collection<T> eles, BinaryFunction<T, T, ? extends Number> comparator)
    {
        if (eles.size() == 0)
            throw new RuntimeException("The input collection is empty");
        var it = eles.iterator();
        var res = it.next();
        while (it.hasNext())
        {
            var ele = it.next();
            if (comparator.apply(ele, res).doubleValue() < 0)
                res = ele;
        }
        return res;
    }

    /**
     * @param col
     * @param valuef
     * @param <T>
     * @return trả lại phần tử trong col có giá trị nhỏ nhất đối với hàm valuef
     */
    public static <T> T minBy(Collection<T> col, UnaryFunction<T, ? extends Number> valuef)
    {
        return min(col, (T x, T y) -> (valuef.apply(x).doubleValue() - valuef.apply(y).doubleValue()));
    }

    /**
     * @param col
     * @param valuef
     * @param <T>
     * @return trả lại phần tử trong col có giá trị lớn nhất đối với hàm valuef
     */
    public static <T> T maxBy(Collection<T> col, UnaryFunction<T, ? extends Number> valuef)
    {
        return max(col,
                (T x, T y) ->
                {
                    return valuef.apply(x).doubleValue() - valuef.apply(y).doubleValue();
                }
        );
    }

    /**
     * @param eles
     * @param <T>
     * @return trả lại phần tử lớn nhất trong các phần tử eles so sánh được với nhau
     */
    public static <T extends Comparable> T max(Collection<T> eles)
    {
        return max(eles,
                (x, y) -> x.compareTo(y)
        );
    }

    /**
     * @param eles
     * @param comparator
     * @param <T>
     * @return trả lại phẩn tử lớn nhất trong eles tương ứng với hàm so sánh comparator
     */
    public static <T> T max(Collection<T> eles, BinaryFunction<T, T, ? extends Number> comparator)
    {
        if (eles.size() == 0)
            throw new RuntimeException("The input collection is empty");
        var it = eles.iterator();
        var res = it.next();
        while (it.hasNext())
        {
            var ele = it.next();
            if (comparator.apply(res, ele).doubleValue() < 0)
                res = ele;
        }
        return res;
    }

    /**
     * áp dụng f lên mỗi cặp phần tử cùng vị trí trong col0 và col1
     *
     * @param f
     * @param col0
     * @param col1
     * @param <S>
     * @param <T>
     */
    public static <S, T> void mapThread(BinaryAction<S, T> f, Collection<S> col0, Collection<T> col1)
    {
        var size = col0.size();
        var it0 = col0.iterator();
        var it1 = col1.iterator();
        while (it0.hasNext())
        {
            var ele0 = it0.next();
            var ele1 = it1.next();
            f.apply(ele0, ele1);
        }
    }

    /**
     * @param f
     * @param col0
     * @param col1
     * @param <S>
     * @param <T>
     * @param <U>
     * @return trả lại danh sách bao gồm các phần tử được áp dụng bởi f vào các phần tử có cùng vị trí col0 và col1
     */
    public static <S, T, U> ArrayList<U> mapThread(BinaryFunction<S, T, U> f, Collection<S> col0, Collection<T> col1)
    {
        var res = new ArrayList<U>();
        if (col0.size() != col1.size())
            throw new RuntimeException("The inputs do not have the same size");
        var it0 = col0.iterator();
        var it1 = col1.iterator();
        while (it0.hasNext())
        {
            var ele0 = it0.next();
            var ele1 = it1.next();
            res.add(f.apply(ele0, ele1));
        }
        return res;
    }

    /**
     * áp dụng f lên mỗi phần tử của arr
     *
     * @param f
     * @param arr
     * @param <S>
     */
    public static <S> void map(UnaryAction<S> f, S[] arr)
    {
        for (var ele : arr)
            f.apply(ele);
    }

    /**
     * áp dụng f lên mỗi phần tử của col
     *
     * @param f
     * @param col
     * @param <S>
     */
    public static <S> void map(UnaryAction<S> f, Collection<S> col)
    {
        for (var ele : col)
            f.apply(ele);
    }

    public static <S, T> ArrayList<T> map(UnaryFunction<S, T> f, S[] arr)
    {
        var res = new ArrayList<T>();
        for (var ele : arr)
            res.add(f.apply(ele));
        return res;
    }

    /**
     * @param f
     * @param col
     * @param <S>
     * @param <T>
     * @return cho ra ArrayList bằng cách áp hàm map cho mỗi phần tử của col
     */
    public static <S, T> ArrayList<T> map(UnaryFunction<S, T> f, Collection<S> col)
    {
        var res = new ArrayList<T>();
        for (var ele : col)
            res.add(f.apply(ele));
        return res;
    }

    /**
     * @param eles
     * @param check
     * @param <T>
     * @return số lượng phần tử trong eles thỏa mãn check
     */
    public static <T> int count(Collection<T> eles, UnaryFunction<T, Boolean> check)
    {
        var res = 0;
        for (var ele : eles)
            if (check.apply(ele))
                res++;
        return res;
    }

    public static <T> boolean anyTrue(T[] array, UnaryFunction<T, Boolean> check)
    {
        for (var ele : array)
            if (check.apply(ele))
                return true;
        return false;
    }

    /**
     * @param eles
     * @param check
     * @param <T>
     * @return trả lại True nếu có bất cứ phần tử nào đúng với hàm kiểm tra check, False otherwise
     */
    public static <T> boolean anyTrue(Collection<T> eles, UnaryFunction<T, Boolean> check)
    {
        var array = (T[]) (Object) eles.toArray();
        return anyTrue(array, check);
    }

    public static <T> boolean allTrue(T[] array, UnaryFunction<T, Boolean> check)
    {
        for (var ele : array)
            if (!check.apply(ele))
                return false;
        return true;
    }

    /**
     * @param eles
     * @param check
     * @param <T>
     * @return trả lại true nếu tất cả các phần tử trong eles thì true với check
     */
    public static <T> boolean allTrue(Collection<T> eles, UnaryFunction<T, Boolean> check)
    {
        var array = (T[]) (Object) eles.toArray();
        return allTrue(array, check);
    }

    /**
     * @param eles
     * @param check
     * @param after
     * @param n
     * @param <S>
     * @param <T>
     * @return trả lại danh sách không quá n phần tử được áp dụng bởi hàm after lên các phần tử trong eles thỏa mãn check
     */
    public static <S, T> ArrayList<T> select(Collection<S> eles, UnaryFunction<S, Boolean> check,
                                             UnaryFunction<S, T> after, int n)
    {
        var res = new ArrayList<T>();
        if (res.size() < n)
        {
            for (var ele : eles)
                if (check.apply(ele))
                {
                    res.add(after.apply(ele));
                    if (res.size() == n)
                        break;
                }
        }
        return res;
    }

    /**
     * @param eles
     * @param check
     * @param after
     * @param <S>
     * @param <T>
     * @return trả lại danh sách các phần tử được áp dụng bởi hàm after lên các phần tử trong eles thỏa mãn check
     */
    public static <S, T> ArrayList<T> select(Collection<S> eles, UnaryFunction<S, Boolean> check, UnaryFunction<S, T> after)
    {
        var res = new ArrayList<T>();
        for (var ele : eles)
            if (check.apply(ele))
                res.add(after.apply(ele));
        return res;
    }

    /**
     * @param eles
     * @param check
     * @param n
     * @param <T>
     * @return một danh sách gồm các phần tử từ eles thỏa mãn check và không vượt quá n phần tử
     */
    public static <T> ArrayList<T> select(Collection<T> eles, UnaryFunction<T, Boolean> check, int n)
    {
        var res = new ArrayList<T>();
        if (res.size() < n)
        {
            for (var ele : eles)
                if (check.apply(ele))
                {
                    res.add(ele);
                    if (res.size() == n)
                        break;
                }
        }
        return res;
    }

    /**
     * @param eles
     * @param check
     * @param <T>
     * @return trả lại một danh sách các phần tử trong eles thỏa mãn hàm kiểm tra check
     */
    public static <T> ArrayList<T> select(Collection<T> eles, UnaryFunction<T, Boolean> check)
    {
        var res = new ArrayList<T>();
        for (var ele : eles)
            if (check.apply(ele))
                res.add(ele);
        return res;
    }

    public static <T extends Comparable<T>> void quickSort(ArrayList<T> eles)
    {
        if (eles.size() == 0)
            return;
        BinaryFunction<T, T, Integer> comparator = (x, y) ->
        {
            var cx = (Comparable<T>) x;
            return cx.compareTo(y);
        };
        quickSort(eles, comparator);
    }

    public static <T> void sortBy(ArrayList<T> eles, UnaryFunction<T, ? extends Number> func)
    {
        quickSort(eles,
                (x, y) -> func.apply(x).doubleValue() - func.apply(y).doubleValue()
        );
    }

    /**
     * chú ý rằng hàm này chỉ được sử dụng đối với Linear order không được dùng cho partial order. Nó chỉ sử dụng
     * được cho partial order nếu x&lt;y và comparator.apply(y,z)==0 thì x&lt;z
     *
     * @param eles
     * @param comparator
     * @param <T>
     */
    public static <T> void quickSort(ArrayList<T> eles, BinaryFunction<T, T, ? extends Number> comparator)
    {
        preQuickSort(eles, 0, eles.size() - 1, comparator);
    }

    private static <T> void preQuickSort(ArrayList<T> eles, int m, int n, BinaryFunction<T, T, ? extends Number> comparator)
    {
        if (eles.size() == 0)
            return;
        if (m == n)
            return;
        var middle = (m + n) / 2;
        preQuickSort(eles, m, middle, comparator);
        preQuickSort(eles, middle + 1, n, comparator);
        var runningIndex0 = m;
        var runningIndex1 = middle + 1;
        var localSorted = new ArrayList<T>();
        while (runningIndex0 <= middle || runningIndex1 <= n)
        {
            T chosenEle;
            if (runningIndex0 > middle)
            {
                chosenEle = eles.get(runningIndex1);
                runningIndex1++;
            } else if (runningIndex1 > n)
            {
                chosenEle = eles.get(runningIndex0);
                runningIndex0++;
            } else
            {
                var ele0 = eles.get(runningIndex0);
                var ele1 = eles.get(runningIndex1);
                if (comparator.apply(ele0, ele1).doubleValue() < 0)
                {
                    chosenEle = ele0;
                    runningIndex0++;
                } else
                {
                    chosenEle = ele1;
                    runningIndex1++;
                }
            }
            localSorted.add(chosenEle);
        }
        for (var i = m; i <= n; i++)
            eles.set(i, localSorted.get(i - m));
    }

    public static <T> void naiveSort(ArrayList<T> eles, BinaryFunction<T, T, Integer> comparator)
    {
        for (var i = 0; i <= eles.size() - 2; i++)
            for (var j = i + 1; j <= eles.size() - 1; j++)
            {
                var iEle = eles.get(i);
                var jEle = eles.get(j);
                if (comparator.apply(iEle, jEle) > 0)
                {
                    var aux = iEle;
                    eles.set(i, jEle);
                    eles.set(j, aux);
                }
            }
    }

    public static <T> void naiveSort(T[] eles, BinaryFunction<T, T, Integer> comparator)
    {
        for (var i = 0; i <= eles.length - 2; i++)
            for (var j = i + 1; j <= eles.length - 1; j++)
            {
                if (comparator.apply(eles[i], eles[j]) > 0)
                {
                    var aux = eles[i];
                    eles[i] = eles[j];
                    eles[j] = aux;
                }
            }
    }

    public static <T> ArrayList<T> join(Collection<T>... cols)
    {
        var res = new ArrayList<T>();
        for (var i = 0; i <= cols.length - 1; i++)
        {
            var icol = cols[i];
            var it = icol.iterator();
            while (it.hasNext())
                res.add(it.next());
        }
        return res;
    }

    public static <T> HashSet<T> union(Collection<T>... sets)
    {
        var res = new HashSet<T>();
        for (var i = 0; i <= sets.length - 1; i++)
        {
            var iset = sets[i];
            var it = iset.iterator();
            while (it.hasNext())
                res.add(it.next());
        }
        return res;
    }

    /**
     * @param set0
     * @param set1
     * @param <T>
     * @return trả lại tập các phần tử có trong set0 mà không có trong set1
     */
    public static <T> HashSet<T> complement(Collection<T> set0, Collection<T> set1)
    {
        var res = new HashSet<T>();
        var it = set0.iterator();
        while (it.hasNext())
        {
            var ele = it.next();
            if (!set1.contains(ele))
                res.add(ele);
        }
        return res;
    }

    /**
     * @param obj một object được sinh bởi sự kết hợp của số tự nhiên, Array,ArrayList, HashSet, HashMap
     * @return
     */
    public static Object copy(Object obj)
    {
        if (obj instanceof Integer)
            return ((Integer) obj).intValue();
        {
            var cl = obj.getClass();
            if (cl.isArray())
            {
                try
                {
                    var objs = Object[].class.cast(obj);
                    var res = new Object[objs.length];
                    for (var i = 0; i <= res.length - 1; i++)
                        res[i] = copy(objs[i]);
                    return res;
                } catch (Exception e)
                {
                    var objs = int[].class.cast(obj);
                    var res = new int[objs.length];
                    for (var i = 0; i <= res.length - 1; i++)
                        res[i] = objs[i];
                    return res;
                }
            }
        }
        if (obj instanceof ArrayList)
        {
            var origin = (ArrayList) obj;
            var res = new ArrayList<>();
            var it = origin.iterator();
            while (it.hasNext())
                res.add(copy(it.next()));
            return res;
        }
        if (obj instanceof HashSet)
        {
            var origin = (HashSet) obj;
            var res = new HashSet<>();
            var it = origin.iterator();
            while (it.hasNext())
                res.add(copy(it.next()));
            return res;
        }
        if (obj instanceof HashMap)
        {
            var origin = (HashMap) obj;
            var res = new HashMap<>();
            var it = origin.keySet().iterator();
            while (it.hasNext())
            {
                var key = it.next();
                var value = origin.get(key);
                res.put(copy(key), copy(value));
            }
            return res;
        }
        return null;
    }

    private static boolean initialize()
    {
        digitStrings = new HashSet<Character>();
        for (var i = 0; i <= 9; i++)
            digitStrings.add(Integer.toString(i).charAt(0));
        try
        {
            loopbackLink = MathLinkFactory.createLoopbackLink();
        } catch (Exception e)
        {
        }
        return true;
    }

    private static boolean isInitialized = initialize();

    public static LoopbackLink loopbackLink;

    private static boolean MListenerInitialized = false;
    private static MathActionListener mathActionListener;
    private static ActionEvent actionEvent;
    public static HashMap<Integer, Object> mathematicaExecutionResult = new HashMap<>();
    private static int mRIndex = -1;

    public static HashMap<Integer, ArrayList<Object>> javaArgs = new HashMap<>();
    private static int jAIndex = -1;
    private static HashSet<Character> digitStrings;

    private static ArrayList<ArrayList<Object>> getArguments(String code)
    {
        var res = new ArrayList<ArrayList<Object>>();
        var runningIndex = 0;
        while (runningIndex <= code.length() - 1)
        {
            var rIEle = code.charAt(runningIndex);
            if (rIEle != '%')
            {
                runningIndex++;
                continue;
            } else
            {
                var snumber = "";
                var i = runningIndex + 1;
                while (i <= code.length() - 1)
                {
                    var iC = code.charAt(i);
                    if (digitStrings.contains(iC))
                    {
                        snumber += Character.toString(iC);
                        i++;
                        continue;
                    } else break;
                }
                if (snumber.length() == 0)
                {
                    runningIndex++;
                    continue;
                } else
                {
                    var pair = new ArrayList<>();
                    pair.add(runningIndex);
                    pair.add(snumber);
                    res.add(pair);
                    runningIndex = i;
                }
            }
        }
        return res;
    }

    private static final String mathKernelPath = "/usr/local/Wolfram/Mathematica/13.0/Executables/MathKernel";
    private static KernelLink kernelLink = null;

    /**
     * hàm này được gọi trong Java mà không cần phải chạy Mathematica như executeMathematicaCode
     *
     * @param expr
     * @return trả lại Expr được thực thi bởi Mathematica đối với expr
     */
    public static Expr evaluateExpr(Expr expr)
    {
        try
        {
            if (kernelLink == null)
            {
                var cmdLine = "-linkmode launch -linkname 'mathKernelPath'";
                cmdLine = cmdLine.replace("mathKernelPath", mathKernelPath);
                kernelLink = MathLinkFactory.createKernelLink(cmdLine);
                kernelLink.discardAnswer();
            }

            kernelLink.evaluate(expr);
            kernelLink.waitForAnswer();
            var result = kernelLink.getExpr();
            return result;
        } catch (Exception e)
        {
            throw new RuntimeException(e.getMessage());
        }
    }

    /**
     * chú ý rằng hàm này được gọi khi chạy Mathematica
     * và nó sẽ thực hiện các biến và giá trị ở Mathematica Notebook
     *
     * @param code mã Mathematica để thực thi. %n trong đoạn code sẽ được thay thế bằng java object thứ n+1 trong jeles
     * @return giá trị được trả lại được thực thi bởi Mathematica
     */
    public static Object executeMathematicaCode(String code, Object... jeles)
    {
        var wcode = code;
        var locs = getArguments(wcode);
        var intLocs = Utilities.makeHashSet(Utilities.map((ArrayList<Object> x) ->
        {
            return Integer.parseInt((String) x.get(1));
        }, locs));
        var maxLoc = locs.size() == 0 ? -1 : Utilities.max(intLocs, (x, y) -> x - y);
        var jelesAr = new ArrayList<Object>();
        if (jeles != null)
        {
            for (var ele : jeles)
                jelesAr.add(ele);
        }
        if (jelesAr.size() == 0)
        {
            if (maxLoc != -1)
                throw new RuntimeException("Invalid input");
        }
        if (jelesAr.size() > 0)
        {
            if (!(maxLoc <= jelesAr.size() - 1))
                throw new RuntimeException("Invalid input");
        }
        jAIndex++;
        javaArgs.put(jAIndex, new ArrayList<>());
        for (var ele : jelesAr)
            javaArgs.get(jAIndex).add(ele);
        {
            var assocCode = "Module[{assoc=<||>,codeHold},Do[assoc[i]=JLink`ReturnAsJavaObject[(Utilities`javaArgs@get[jAIndex//JLink`MakeJavaObject])@get[i]],{i,0,length-1}];codeHold=Hold[wcode]/.HoldPattern[assoc]->assoc;ReleaseHold@codeHold]";
            var rules = new HashMap<String, String>();
            for (var i = 0; i <= locs.size() - 1; i++)
            {
                var iEle = locs.get(i);
                var number = (String) iEle.get(1);
                var inserted = "assoc[pos]";
                var auxRules = new HashMap<String, String>();
                auxRules.put("pos", number);
                inserted = stringReplace(inserted, auxRules);
                rules.put("%" + number, inserted);
            }
            wcode = stringReplace(wcode, rules);
            rules.clear();
            rules.put("wcode", wcode);
            rules.put("length", Integer.toString(javaArgs.get(jAIndex).size()));
            rules.put("jAIndex", Integer.toString(jAIndex));
            wcode = stringReplace(assocCode, rules);
        }

        if (!MListenerInitialized)
        {
            mathActionListener = new MathActionListener();
            actionEvent = new ActionEvent(new Object(), -1, null);
            MListenerInitialized = true;
        }
        mRIndex++;
        var storedMRIndex = mRIndex;
        var newCode = "Utilities`mathematicaExecutionResult@put[storedMRIndex//JLink`MakeJavaObject,Module[{res},res=(code);Utilities`javaArgs@remove[jAIndex//JLink`MakeJavaObject];If[JLink`JavaObjectQ[res],res,JLink`MakeJavaExpr[res]]]]";
        {
            var rules = new HashMap<String, String>();
            rules.put("code", wcode);
            rules.put("storedMRIndex", Integer.toString(storedMRIndex));
            rules.put("jAIndex", Integer.toString(jAIndex));
            newCode = stringReplace(newCode, rules);
        }
        mathActionListener.setHandler("actionPerformed", newCode);
        mathActionListener.actionPerformed(actionEvent);
        var res = mathematicaExecutionResult.get(storedMRIndex);
        mathematicaExecutionResult.remove(storedMRIndex);
        return res;
    }

    public static void auxTest(HashMap h0, HashMap h1, Collection col)
    {
        Utilities.executeMathematicaCode("Echo@\"changed\"");
    }
}

class BinaryFunctionClass<S, T, R> implements BinaryFunction<S, T, R>
{

    private BinaryFunction<S, T, R> func;

    public BinaryFunctionClass(BinaryFunction<S, T, R> ifunc)
    {
        this.func = ifunc;
    }

    @Override
    public R apply(S s, T t)
    {
        return func.apply(s, t);
    }
}

class UnaryFunctionClass<S, T> implements UnaryFunction<S, T>
{

    public UnaryFunctionClass(UnaryFunction<S, T> ifunc)
    {
        this.func = ifunc;
    }

    private UnaryFunction<S, T> func;

    @Override
    public T apply(S s)
    {
        return func.apply(s);
    }
}