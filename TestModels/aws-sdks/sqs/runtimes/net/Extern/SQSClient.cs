using Amazon;
using Amazon.SQS;
using Wrappers_Compile;
using Amazon.Runtime;
using Com.Amazonaws.Sqs;

// This extern is identified in Dafny code
// that refines the AWS SDK SQS Model
namespace Dafny.Com.Amazonaws.Sqs
{
  public partial class __default
  {
    
    public static
      _IResult<
        Types.ISQSClient,
        Types._IError
      >
      SQSClient()
    {
      var client = new SQSClient();

      return Result<
        Types.ISQSClient,
        Types._IError
      >
        .create_Success(new SQSShim(client));
    }
  }
}