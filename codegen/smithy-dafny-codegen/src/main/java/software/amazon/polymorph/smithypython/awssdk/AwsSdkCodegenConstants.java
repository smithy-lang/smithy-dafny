package software.amazon.polymorph.smithypython.awssdk;

public class AwsSdkCodegenConstants {
    public static String AWS_SDK_CODEGEN_SYMBOLWRITER_DUMP_FILE_FILENAME = "awssdk_codegen_todelete.tmp";

    // boto3 models `Timestamp` Smithy objects as `datetime.datetime` objects
    // with millisecond precision masquerading as microsecond precision;
    // e.x. datetime.datetime(2024, 6, 14, 16, 40, 15, 761000, tzinfo=tzlocal())
    // --> 761000 is actually just 761 ms, but boto3 reports it with microsecond precision.
    public static String BOTO3_TIMESTAMP_STRING_FORMAT = "%Y-%m-%dT%H:%M:%S.%fZ";
}
