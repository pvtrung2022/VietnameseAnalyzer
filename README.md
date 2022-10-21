Dự án này được dùng để phân tích cấu trúc câu tiếng Việt một cách tự động.

Dự án GitHub này bao gồm hai dự án IntelliJ IDEA là VietnameseAnalyzer và Utilities trong các thư mục tương ứng. Dự án thứ nhất là dự án chính và tham chiếu đến dự án thứ hai. Trong quá trình thực hiện dự án có sử dụng jlink của Mathematica để tham chiếu nên khi sử dụng bạn cần phải tham chiếu hai dự án này đến thư viện JLink.jar để tránh báo lỗi. Thực tế thì bạn không cần phải biết cách sử dụng thư viện này bởi vì các hàm chính để chạy chương trình không tham chiếu đến thư viện này. Bạn chỉ cần tải các dự án về đặt trong một thư mục và dùng IntelliJ IDEA để mở dự án chính, sau đó mở cài đặt trong File->Project Structure của IntelliJ IDEA để tham chiếu hai module VietnameseAnalyzer và Utilities đến thư viện JLink.jar.

Để chạy chương trình đầu tiên bạn sẽ gọi VietnameseAnalyzer.initialize() để chương trình tải những thông tin cần thiết vào các biến tĩnh. Quá trình này thường mất khoảng dưới 2 phút. Sau đó gọi Vietnamese.decideParser(sentence) với sentence là câu bất kỳ bạn nhập vào sẽ cho ra cấu trúc ngữ pháp phụ thuộc của câu (Dependency grammar) dưới dạng một đối tượng đồ thị thược lớp Parser được thiết lập trong dự án VietnameseAnalyzer. Vì hàm tĩnh VietnameseAnalyzer.initialize() tải các thông tin cần thiết vào các biến tĩnh nên bạn chỉ cần gọi một lần trong suốt quá trình hoạt động của Java. 

Trong quá trình phân tích một câu nhập vào chương trình sẽ tự động tách câu để chọn từ và chọn kiểu từ loại cho từ. Ví dụ như chương trình sẽ tự động chọn kiểu từ loại cho từ là danh từ ("N"), động từ (""V) hoặc tính từ ("A"), etc. Trong trường hợp bạn không hài lòng với quá trình chọn tự động ấy bạn có thể nhập câu theo mảng để tự mình chọn từ và kiểu từ loại của từ. 

Vì kho dữ liệu huấn luyện không quá lớn nên có nhiều từ Tiếng Việt không có trong dữ liệu huấn luyện. Để kiểm tra một từ có trong kho huấn luyện và các kiểu ngữ pháp của từ cũng như số lần xuất hiện trong kho huấn luyện, bạn có thể dùng biến tĩnh VietnameseAnalyzer.WordAppearances để kiểm tra. Biến này là một HashMap nên có thể gọi VietnameseAnalyzer.WordAppearances.keySet() để cho ra tập tất cả các từ có trong kho dữ liệu huấn luyện. Trong trường hợp bạn muốn dùng một từ không có trong kho dữ liệu thì có thể thay thế nó bằng một từ tương tự có trong kho dữ liệu. 

Để minh họa cụ thể hơn cho hướng dẫn bạn vui lòng chạy chương trình trong file Test.java trong dự án VietnameseAnalyzer của IntelliJ IDEA.

Dự án này được thực hiện trên IntelliJ IDEA 2022.2.3 và Java 11.0.15
