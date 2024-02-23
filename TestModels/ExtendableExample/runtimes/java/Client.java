

// API skeleton

public class AWSCredentials {

  private final String username;
  private final String password;

  public AWSCredentials(String username, String password) {
    this.username = username;
    this.password = password;
  }

  public String getUserName() {
    return username;
  }

  public String getPassword() {
    return password;
  }
}

public interface AWSCredentialsProvider {
  public AWSCredentials getCredentials();
}

public interface SQSExtendedClient {
  
  public AWSCredentialsProvider createDefaultCredentialsProvider();

  public String createQueue(AWSCredentialsProvider credentialsProvider,
                            String queueName);

  public void sendMessageThroughS3(AWSCredentialsProvider credentialsProvider,
                                   String queueUrl,
                                   String message);

  public String receiveMessageThroughS3(AWSCredentialsProvider credentialsProvider,
                                        String queueUrl);
}

// Implementation

// Disclaimer: I have played very fast and loose with the actual
// SQS and S3 APIs, and the actual structure of Java SDKs,
// in the name of simplicity.
// In the real world you would also create service clients on initialization
// and reuse them, and I'm leaving out tons of detail on the actual client implementation.
class SQSExtendedClientImpl implements SQSExtendedClient {

  public AWSCredentialsProvider createDefaultCredentialsProvider() {
    return DefaultCredentialsProviderChain.create();
  }

  public String createQueue(AWSCredentialsProvider credentialsProvider,
                            String queueName) {
    SQS sqsClient = new SQSClient(credentialsProvider);
    return sqsClient.createQueue(queueName);
  }

  public void sendMessageThroughS3(AWSCredentialsProvider credentialsProvider,
                                   String queueUrl,
                                   String message) {
    S3 s3Client = new S3Client(credentialsProvider);
    String keyName = generateNewKeyName();                               
    // The Bucket name would normally be configurable too
    s3Client.putObject("SQSMessages", keyName, message);
                                    
    SQS sqsClient = new SQSClient(credentialsProvider);
    sqsClient.sendMessage(keyName);
  }

  public String receiveMessageThroughS3(AWSCredentialsProvider credentialsProvider,
                                        String queueUrl) {
    SQS sqsClient = new SQSClient(credentialsProvider);
    String keyName = sqsClient.receiveMessage(queueUrl);

    S3 s3Client = new S3Client(credentialsProvider);
    String message = s3Client.getObject("SQSMessages", keyName);
    s3Client.deleteObject(s3ObjectId);

    return message;
  }
}