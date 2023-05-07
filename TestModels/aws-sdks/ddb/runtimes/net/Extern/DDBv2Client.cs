using Amazon;
using Amazon.DynamoDBv2;
using Wrappers_Compile;
using Amazon.Runtime;
using Com.Amazonaws.Dynamodb;

// This extern is identified in Dafny code
// that refines the AWS SDK DDB Model
namespace software.amazon.awssdk.services.dynamodb.internaldafny
{
  public partial class __default
  {
    public static
        _IResult<
            Types.IDynamoDBClient,
            Types._IError
        >
        DynamoDBClient()
    {
      var client = new AmazonDynamoDBClient();

      return Result<
              Types.IDynamoDBClient,
              Types._IError
          >
          .create_Success(new DynamoDBv2Shim(client));
    }
  }
}
