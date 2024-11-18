use compolabs_sway_libs::signed_integers::i64::{I64, INDENT_I64};

#[tokio::test]
async fn test_bits() -> anyhow::Result<()> {
    assert_eq!(I64::bits(), 64);

    Ok(())
}

#[tokio::test]
async fn test_max() -> anyhow::Result<()> {
    assert_eq!(I64::max().underlying(), u64::MAX);

    Ok(())
}

#[tokio::test]
async fn test_min() -> anyhow::Result<()> {
    assert_eq!(I64::min().underlying(), 0);

    Ok(())
}

#[tokio::test]
async fn test_new() -> anyhow::Result<()> {
    assert_eq!(I64::new().underlying(), INDENT_I64);

    Ok(())
}

#[tokio::test]
async fn test_zero() -> anyhow::Result<()> {
    assert_eq!(I64::zero().underlying(), INDENT_I64);

    Ok(())
}

#[tokio::test]
async fn test_is_zero() -> anyhow::Result<()> {
    assert!(I64::zero().is_zero());

    Ok(())
}

#[tokio::test]
async fn test_underlying() -> anyhow::Result<()> {
    assert_eq!(I64::zero().underlying(), INDENT_I64);

    Ok(())
}

#[tokio::test]
async fn test_is_negative() -> anyhow::Result<()> {
    assert!(I64::min().is_negative());

    Ok(())
}

#[tokio::test]
async fn test_is_positive() -> anyhow::Result<()> {
    assert!(I64::max().is_positive());

    Ok(())
}

#[tokio::test]
async fn test_from() -> anyhow::Result<()> {
    assert_eq!(I64::from(1u64).underlying(), INDENT_I64 + 1);

    Ok(())
}

#[tokio::test]
async fn test_abs() -> anyhow::Result<()> {
    assert_eq!(I64::min().abs(), INDENT_I64);
    assert_eq!(I64::max().abs(), INDENT_I64 - 1);

    Ok(())
}

#[tokio::test]
async fn test_reverse_sign() -> anyhow::Result<()> {
    assert_eq!(I64::max().reverse_sign().underlying(), 1);

    Ok(())
}

#[tokio::test]
async fn test_reverse_sign_if() -> anyhow::Result<()> {
    assert_eq!(I64::max().reverse_sign_if(true).underlying(), 1);
    assert_eq!(I64::max().reverse_sign_if(false).underlying(), u64::MAX);

    Ok(())
}
