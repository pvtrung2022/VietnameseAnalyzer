package vietnameseanalyzer;

import com.trung.*;

public class Test
{
    public static void main(String[] argv)
    {
        System.out.println("bắt đầu việc tải các thông tin cần thiết");
        VietnameseAnalyzer.initialize();
        System.out.println("hoàn tất việc tải các thông tin cần thiết");

        // đây là trường hợp nhập câu trực tiếp
        {
            var sentence = "tôi yêu cô ấy rất nhiều";
            var parser = VietnameseAnalyzer.decideParser(sentence);
            System.out.println("in kết quả cho trường hợp nhập câu trực tiếp");
            System.out.println(parser);
        }

        // đây là trường hợp nhập câu theo mảng
        {
            var sentence = new String[][]{
                    {"tôi", "P"},
                    {"yêu", "V"},
                    {"cô", "N"},
                    {"ấy", "P"},
                    {"rất", "R"},
                    {"nhiều", "A"}
            };
            var parser = VietnameseAnalyzer.decideParser(sentence);
            System.out.println("in kết quả cho trường hợp nhập câu theo mảng");
            System.out.println(parser);
        }

        // kiểm tra một từ có trong dữ liệu huấn luyện hay không
        {
            var word = "chăm chỉ";
            var check = VietnameseAnalyzer.WordAppearances.containsKey(word);
            if (check)
            {
                System.out.println("từ '" + word + "'" + " này có trong dữ liệu huấn luyện");
                System.out.println("các kiểu ngữ pháp của từ này là: " +
                        VietnameseAnalyzer.WordAppearances.get(word).keySet()
                );
                System.out.println("số lần xuất hiện của từ này trong dữ liệu huấn luyện: " +
                        VietnameseAnalyzer.WordAppearances.get(word)
                );
            } else System.out.println("từ này không có trong dữ liệu huấn luyện");
        }
    }
}
